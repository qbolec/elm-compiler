{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-}
module Type.State where

import qualified Control.Monad.State as State
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as Map
import qualified Data.UnionFind.IO as UF
import Data.List (foldl')

import qualified Reporting.Annotation as A
import qualified Reporting.Error.Type as Error
import qualified Reporting.Region as R
import Type.Type

-- Pool
-- Holds a bunch of variables
-- The rank of each variable is less than or equal to the pool's "maxRank"
-- The young pool exists to make it possible to identify these vars in constant time.

data Pool = Pool
    { maxRank :: Int
    , inhabitants :: [Variable]
    }


emptyPool :: Pool
emptyPool =
    Pool
    { maxRank = outermostRank
    , inhabitants = []
    }


type Env = Map.Map String (A.Located Variable)


type Solver = State.StateT SolverState IO


-- Keeps track of the environment, type variable pool, and a list of errors
data SolverState = SS
    { sEnv :: Env
    , sSavedEnv :: Env
    , sPool :: Pool
    , sMark :: Int
    , sError :: [A.Located Error.Error]
    }


initialState :: SolverState
initialState =
    SS
    { sEnv = Map.empty
    , sSavedEnv = Map.empty
    , sPool = emptyPool
    , sMark = noMark + 1  -- The mark must never be equal to noMark!
    , sError = []
    }


modifyEnv :: (Env -> Env) -> Solver ()
modifyEnv f =
    State.modify $ \state -> state { sEnv = f (sEnv state) }


modifyPool :: (Pool -> Pool) -> Solver ()
modifyPool f =
    State.modify $ \state -> state { sPool = f (sPool state) }


addError :: R.Region -> Error.Error -> Solver ()
addError region err =
    State.modify $ \state -> state { sError = A.A region err : sError state }


switchToPool :: Pool -> Solver ()
switchToPool pool =
    modifyPool (\_ -> pool)


getPool :: Solver Pool
getPool =
    State.gets sPool


getEnv :: Solver Env
getEnv =
    State.gets sEnv


saveLocalEnv :: Solver ()
saveLocalEnv =
  do  currentEnv <- getEnv
      State.modify $ \state -> state { sSavedEnv = currentEnv }


uniqueMark :: Solver Int
uniqueMark =
  do  state <- State.get
      let mark = sMark state
      State.put $ state { sMark = mark + 1 }
      return mark


nextRankPool :: Solver Pool
nextRankPool =
  do  pool <- getPool
      return $ Pool { maxRank = maxRank pool + 1, inhabitants = [] }


register :: Variable -> Solver Variable
register !variable = {-# SCC "!register" #-}
  do  modifyPool $ \pool -> pool { inhabitants = variable : inhabitants pool }
      return variable


introduce :: Variable -> Solver Variable
introduce variable = {-# SCC "!introduce" #-}
  do  pool <- getPool
      State.liftIO $ UF.modifyDescriptor variable (\desc -> desc { _rank = maxRank pool })
      register variable


flatten :: Type -> Solver Variable
flatten !term = {-# SCC "!flatten" #-}
  -- do  !x <- flattenHelp Map.empty term
  --     let !s = measureVariable x
  --     return x
  flattenHelp Map.empty term

flattenHelp :: Map.Map String Variable -> Type -> Solver Variable
flattenHelp !aliasDict !termN = {-# SCC "!flattenHelp" #-}
--   do  v <- flattenHelpAux aliasDict termN
--       let !s = measureVariable v
--       return v

-- flattenHelpAux !aliasDict !termN = {-# SCC "!flattenHelpAux" #-}
  case termN of
    PlaceHolder !name ->
        let !lookedUp = (aliasDict ! name)
        in
          return lookedUp

    AliasN !name !args !realType ->
        do  !flatArgs <- {-# SCC "!AliasN.flatArgs" #-} mapM (\ !x -> let !t = traverse (\ !y -> let !z = flattenHelp aliasDict y in z) x in t) args
            let !bla = {-# SCC "!AliasN.bla" #-} length flatArgs
            !flatVar <- {-# SCC "!AliasN.flatVar" #-} flattenHelp (Map.fromList flatArgs) realType
            !pool <- getPool
            let !theContent = {-# SCC "!AliasN.theContent" #-} Alias name flatArgs flatVar
            -- let !theContentSize = {-# SCC "!AliasN.theContentSize" #-} measureContent theContent
            let !theDescriptor = {-# SCC "!AliasN.theDescriptor" #-} Descriptor
                  { _content = theContent
                  , _rank = maxRank pool
                  , _mark = noMark
                  , _copy = Nothing
                  }
            let !fr = {-# SCC "!AliasN.fr" #-} UF.fresh theDescriptor
            !variable <- {-# SCC "!AliasN.variable" #-} State.liftIO fr
            {-# SCC "!AliasN.register" #-} register variable

    VarN !v ->
        return v

    TermN !term1 ->
        do  !variableTerm <- {-# SCC "!TermN.variableTerm" #-} traverseTerm (flattenHelp aliasDict) term1
            -- let !bla = measure1 variableTerm measureVariable
            !pool <- getPool
            let !theContent =  {-# SCC "!TermN.theContent" #-} Structure variableTerm
            -- let !theContentSize = {-# SCC "!TermN.theContentSize" #-}  measureContent theContent
            let !theDescriptor = {-# SCC "!TermN.theDescriptor" #-}  Descriptor
                  { _content = theContent
                  , _rank = maxRank pool
                  , _mark = noMark
                  , _copy = Nothing
                  }
            let !fr = {-# SCC "!TermN.fr" #-} UF.fresh theDescriptor
            !variable <- {-# SCC "!TermN.variable" #-} State.liftIO fr
            {-# SCC "!TermN.register" #-} register variable


makeInstance :: Variable -> Solver Variable
makeInstance var =
  do  alreadyCopiedMark <- uniqueMark
      freshVar <- makeCopy alreadyCopiedMark var
      _ <- restore alreadyCopiedMark var
      return freshVar


makeCopy :: Int -> Variable -> Solver Variable
makeCopy alreadyCopiedMark variable =
  do  desc <- State.liftIO $ UF.descriptor variable
      makeCopyHelp desc alreadyCopiedMark variable


makeCopyHelp :: Descriptor -> Int -> Variable -> Solver Variable
makeCopyHelp descriptor alreadyCopiedMark variable = {-# SCC "!makeCopyHelp" #-}
  if _mark descriptor == alreadyCopiedMark then
      case _copy descriptor of
        Just copiedVariable ->
            return copiedVariable

        Nothing ->
            error
              "Error copying type variable. This should be impossible.\
              \ Please report this at <https://github.com/elm-lang/elm-compiler/issues>\
              \ with a <http://sscce.org> and information on your OS, how you installed,\
              \ and any other configuration information that might be helpful."

  else if _rank descriptor /= noRank || not (needsCopy (_content descriptor)) then
      return variable

  else
      do  pool <- getPool
          newVar <-
              State.liftIO $ UF.fresh $ Descriptor
                -- { _content = error "will be filled in soon!"
                { _content = Error
                , _rank = maxRank pool
                , _mark = noMark
                , _copy = Nothing
                }
          _ <- register newVar

          -- Link the original variable to the new variable. This lets us
          -- avoid making multiple copies of the variable we are instantiating.
          --
          -- Need to do this before recursively copying the content of
          -- the variable to avoid looping on cyclic terms.
          State.liftIO $ UF.modifyDescriptor variable $ \desc ->
              desc { _mark = alreadyCopiedMark, _copy = Just newVar }

          -- Now we recursively copy the content of the variable.
          -- We have already marked the variable as copied, so we
          -- will not repeat this work or crawl this variable again.
          let oldContent = _content descriptor
          newContent <-
              case oldContent of
                Structure term ->
                    Structure <$> traverseTerm (makeCopy alreadyCopiedMark) term

                Atom _ ->
                    return oldContent

                Var Rigid maybeSuper _ ->
                    return (Var Flex maybeSuper Nothing)

                Var Flex _ _ ->
                    return oldContent

                Alias name args realType ->
                    Alias name
                        <$> mapM (traverse (makeCopy alreadyCopiedMark)) args
                        <*> makeCopy alreadyCopiedMark realType

                Error ->
                    return oldContent

          State.liftIO $ UF.modifyDescriptor newVar $ \desc ->
              desc { _content = newContent }

          return newVar


needsCopy :: Content -> Bool
needsCopy content =
  case content of
    Structure _ ->
        True

    Atom _ ->
        False

    Var _ _ _ ->
        True

    Alias _ _ _ ->
        True

    Error ->
        False



restore :: Int -> Variable -> Solver Variable
restore alreadyCopiedMark variable =
  do  desc <- State.liftIO $ UF.descriptor variable
      if _mark desc /= alreadyCopiedMark
        then
          return variable

        else
          do  restoredContent <-
                  restoreContent alreadyCopiedMark (_content desc)
              State.liftIO $ UF.setDescriptor variable $ Descriptor
                  { _content = restoredContent
                  , _rank = noRank
                  , _mark = noMark
                  , _copy = Nothing
                  }
              return variable



restoreContent :: Int -> Content -> Solver Content
restoreContent alreadyCopiedMark content =
  let
    go = restore alreadyCopiedMark
  in
  case content of
    Structure term ->
        Structure <$> traverseTerm go term

    Atom _ ->
        return content

    Var _ _ _ ->
        return content

    Alias name args var ->
        Alias name
          <$> mapM (traverse go) args
          <*> go var

    Error ->
        return content



-- TERM TRAVERSAL

measure1 :: Term1 a -> (a -> IO Int) -> IO Int
measure1 term1 m =
  case term1 of
    App1 !a !b ->
      do  ma <- m a
          mb <- m b
          return $ ma + mb

    Fun1 !a !b ->
      do  ma <- m a
          mb <- m b
          return $ ma + mb

    EmptyRecord1 ->
        return 1

    Record1 !fields !ext ->
        do  x <- (Map.foldl' (\ n !c-> do { mc <- m c; nn <- n; return $ nn + mc } ) (return 1) fields)
            mext <- m ext
            return $  x + mext

-- measureN :: TermN a -> Int
-- measureN termN =
--   case termN of
--     PlaceHolder !name ->
--       1
--     AliasN !can !list !t ->
--       ( foldl' (\ n (!name, !c)  -> n + measureN c ) 1 list ) + (measureN t)
--     VarN !a ->
--       1
--     TermN !t ->
--       measure1 t measureN

measureVariable :: Variable -> IO Int
measureVariable variable =
  -- measureContent (_content <$> UF.descriptor variable)
  do  desc <- State.liftIO $ UF.descriptor variable
      let co = _content desc
      measureContent co

measureContent :: Content -> IO Int
measureContent content =
  case content of
    Structure !variable ->
      measure1 variable measureVariable
    Atom !v ->
      return $ 1
    Var !f !super !str ->
      return $ 1
    Alias !v !namedVariables !variable ->
      do  mv <- measureVariable variable
          x <- (foldl' (\ n (!name, !c)  -> do { nn <- n; mc <- measureVariable c; return $ nn + mc} ) (return 1) namedVariables)
          return $  x + mv
    Error ->
      return $ 0

traverseTerm :: (Monad f, Applicative f) => (a -> f b) -> Term1 a -> f (Term1 b)
traverseTerm !s !term = {-# SCC "!traverseTerm" #-}
  case term of
    App1 !x !y ->  {-# SCC "!App1" #-}
        do  !sx <- {-# SCC "!App1sx" #-} s x
            !sy <- {-# SCC "!App1sy" #-} s y
            return (App1 sx sy )

    Fun1 !x !y -> {-# SCC "!Fun1" #-}
        do  !sx <- {-# SCC "!Fun1sx" #-} s x
            !sy <- {-# SCC "!Fun1sy" #-} s y
            return (Fun1 sx sy )

    EmptyRecord1 -> {-# SCC "!EmptyRecord1" #-}
        return EmptyRecord1

    Record1 !fields !ext -> {-# SCC "!Record1" #-}
        do  !sext <- {-# SCC "!sext" #-} s ext
            !sfields <- {-# SCC "!sfields" #-} traverse s fields
            let !sfiledsSize = {-# SCC "!sfiledsSize" #-} Map.size sfields
            return (Record1 sfields sext )

-- --   a <$> b <*> c   =  do { fb <- b ; fc <- c ; return $ a fb fc }

-- traverseTerm !f !term =
--   case term of
--     App1 !a !b ->
--         App1 <$> f a <*> f b

--     Fun1 !a !b ->
--         Fun1 <$> f a <*> f b

--     EmptyRecord1 ->
--         return EmptyRecord1

--     Record1 !fields !ext ->
--         Record1 <$> traverse f fields <*> f ext
