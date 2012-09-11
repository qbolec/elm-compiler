var Guid=function(){var d=0;return{guid:function(){return d+=1}}}(),Foreign=function(){var d=function(a){for(var c=["Nil"],b=a.length;b--;)c=["Cons",a[b],c];return c},b=function(a){for(var c=[];"Cons"===a[0];)c.push(a[1]),a=a[2];return c},c=function(a){return a.slice(1)},a=function(a){return["Tuple"+a.length].concat(a)};return{JavaScript:{castJSBoolToBool:function(a){return a},castBoolToJSBool:function(a){return a},castJSNumberToFloat:function(a){return a},castFloatToJSNumber:function(a){return a},
castJSNumberToInt:function(a){return~~a},castIntToJSNumber:function(a){return a},Experimental:{castJSElementToElement:function(a){return Element.jsElement(a)},castElementToJSElement:function(a){return a}},castJSArrayToList:d,castListToJSArray:b,castJSStringToString:d,castStringToJSString:function(a){return"string"===typeof a?a:b(a).join("")},castTupleToJSTuple2:c,castTupleToJSTuple3:c,castTupleToJSTuple4:c,castTupleToJSTuple5:c,castJSTupleToTuple2:a,castJSTupleToTuple3:a,castJSTupleToTuple4:a,castJSTupleToTuple5:a}}}(),
ElmJSON=function(){function d(a){return function(g){function b(a){switch(a[0]){case "JsonNull":return null;case "JsonString":return c.castStringToJSString(a[1]);case "JsonObject":var g={},a=a[1][1],d;for(d in a)g[d]=b(a[d]);return g;case "JsonArray":g=c.castListToJSArray(a[1]);for(d=g.length;d--;)g[d]=b(g[d]);return g;default:return a[1]}}return JSON.stringify(b(["JsonObject",g]),null,c.castStringToJSString(a))}}function b(a){function g(a){switch(typeof a){case "string":return["JsonString",c.castJSStringToString(a)];
case "number":return["JsonNumber",c.castJSNumberToFloat(a)];case "boolean":return["JsonBool",c.castJSBoolToBool(a)];case "object":if(null===a)return["JsonNull"];for(var b in a)a[b]=g(a[b]);return a instanceof Array?["JsonArray",c.castJSArrayToList(a)]:["JsonObject",["JSON",a]]}}var a=JSON.parse(a),b;for(b in a)a[b]=g(a[b]);return["JSON",a]}var c=Foreign.JavaScript;return{empty:["JSON",{}],singleton:function(a){return function(g){var b={};b[c.castStringToJSString(a)]=g;return["JSON",b]}},insert:function(a){return function(g){return function(b){var b=
b[1],d={},i;for(i in b)d[i]=b[i];d[c.castStringToJSString(a)]=g;return["JSON",d]}}},lookup:function(a){return function(b){var f=c.castStringToJSString(a);return b[1].hasOwnProperty(f)?Just(b[1][f]):Nothing}},findWithDefault:function(a){return function(b){return function(f){var d=c.castStringToJSString(b);return f[1].hasOwnProperty(d)?f[1][d]:a}}},remove:function(a){return function(b){var b=b[1],f={},d;for(d in b)f[d]=b[d];delete f[c.castStringToJSString(a)];return["JSON",f]}},toPrettyJSString:d,toJSString:d(""),
fromJSString:b,toPrettyString:function(a){return function(b){return c.castJSStringToString(d(a)(b))}},toString:function(a){return c.castJSStringToString(d("")(a))},fromString:function(a){return b(c.castStringToJSString(a))},toList:function(a){var a=a[1],b=[],d;for(d in a)b.push(Value.Tuple(c.castJSStringToString(d),a[d]));return c.castJSArrayToList(b)},fromList:function(a){for(var a=c.castListToJSArray(a),b={},d=a.length;d--;)b[c.castStringToJSString(a[d][1])]=a[d][2];return["JSON",b]},JsonString:function(a){return["JsonString",
a]},JsonNumber:function(a){return["JsonNumber",a]},JsonBool:function(a){return["JsonBool",a]},JsonNull:["JsonNull"],JsonArray:function(a){return["JsonArray",a]},JsonObject:function(a){return["JsonObject",a]}}}();Foreign.JavaScript.JSON=ElmJSON;
var Value=function(){function d(a){if(0==a.length)return a;for(var a=a.replace(/"/g,"&#34;").replace(/'/g,"&#39;").replace(/</g,"&#60;").replace(/>/g,"&#62;").replace(/\n/g,"<br/>"),a=a.split("<br/>"),c=a.length;c--;){var b=a,d=c,i;i=a[c].split("");" "==i[0]&&(i[0]="&nbsp;");for(var j=i.length;--j;)" "==i[j][0]&&" "==i[j-1]&&(i[j-1]+=i[j],i[j]="");for(j=i.length;j--;)if(1<i[j].length&&" "==i[j][0]){for(var h=i[j].split(""),m=h.length-2;0<=m;m-=2)h[m]="&nbsp;";i[j]=h.join("")}i=i.join("");b[d]=i}return a.join("<br/>")}
var b=function(a,c){if("object"===typeof a){if(a===c)return!0;if(a.length!==c.length)return!1;for(var d=a.length;d--;)if(!b(a[d],c[d]))return!1;return!0}return a===c},c=function(a){if("boolean"===typeof a)return a?"True":"False";if("number"!==typeof a){if("string"===typeof a&&2>a.length)return"'"+a+"'";if(a[0]){if("Tuple"===a[0].substring(0,5)){for(var b="",d=a.length;--d;)b=","+c(a[d])+b;","===b[0]&&(b=b.substring(1));return"("+b+")"}if("Cons"===a[0])for(var d="string"===typeof a[1]?'"':"]",k="string"===
typeof a[1]?"":",",i="string"===typeof a[1]?function(a){return a}:c,b=("string"===typeof a[1]?'"':"[")+i(a[1]),a=a[2];;)if("Cons"===a[0])b+=k+i(a[1]),a=a[2];else return b+d;else{if("Nil"===a[0])return"[]";if("JSON"===a[0])return"(JSON.fromList "+c(ElmJSON.toList(a))+")";b="";for(d=a.length;--d;)b=" "+c(a[d])+b;b=a[0]+b;return 1<a.length?"("+b+")":b}}}return a+""};return{eq:b,str:function(a){for(var b=["Nil"],c=a.length;c--;)b=["Cons",a[c],b];return b},show:function(a){return Text.monospace(d(c(a)))},
Tuple:function(){var a=arguments.length,b=Array(a+1);for(b[0]="Tuple"+arguments.length;a--;)b[a+1]=arguments[a];return b},append:function(a,b){if("string"===typeof a&&"string"===typeof b)return a.concat(b);if("Nil"===a[0])return b;for(var c=["Cons",a[1],["Nil"]],d=c,a=a[2];"Cons"===a[0];)d[2]=["Cons",a[1],["Nil"]],a=a[2],d=d[2];d[2]=b;return c},listToArray:function(a){for(var b=[];"Cons"===a[0];)b.push(a[1]),a=a[2];return b},toText:function(a){if("string"===typeof a)return d(a);for(var b=[];"Cons"===
a[0];)b.push(a[1]),a=a[2];return d(b.join(""))},properEscape:d}}(),List=function(){function d(a){return function(e){if("Nil"===e[0])return e;"Cons"!==e[0]&&h("map");for(var b=["Cons",a(e[1]),["Nil"]],c=b,e=e[2];"Cons"===e[0];)c[2]=["Cons",a(e[1]),["Nil"]],e=e[2],c=c[2];return b}}function b(a){return function(e){return function(b){var c=e;if("Nil"===b[0])return c;for("Cons"!==b[0]&&h("foldl");"Cons"===b[0];)c=a(b[1])(c),b=b[2];return c}}}function c(a){return function(e){return function(b){var c=e;
if("Nil"===b[0])return c;"Cons"!==b[0]&&h("foldr");for(var d=[];"Cons"===b[0];)d.push(b[1]),b=b[2];for(b=d.length;b--;)c=a(d[b])(c);return c}}}function a(a){return function(e){var c;"Cons"!==e[0]?c=void 0:(c=e[1],e=e[2],c=b(a)(c)(e));return c}}function g(a){return function(e){return function(b){if("Nil"===b[0])return["Cons",e,["Nil"]];"Cons"!==b[0]&&h("scanl");for(var c=[e];"Cons"===b[0];)e=a(b[1])(e),c.push(e),b=b[2];for(var b=["Nil"],d=c.length;d--;)b=["Cons",c[d],b];return b}}}function f(a){return function(e){a:{for(var b=
[function(a){return"Nil"!==a[0]?void 0:["Tuple2",["Nil"],["Nil"]]},function(e){if("Cons"===e[0]){var b=e[1],e=e[2];var c=f(a)(e);"Tuple2"!==c[0]?b=void 0:(e=c[1],c=c[2],b=a(b)?["Tuple2",["Cons",b,e],c]:["Tuple2",e,["Cons",b,c]]);return b}}],c=b.length;c--;){var d=b[c](e);if(void 0!==d){e=d;break a}}e=void 0}return e}}function k(a){a:{for(var e=[function(a){return"Nil"!==a[0]?void 0:["Tuple2",["Nil"],["Nil"]]},function(a){if("Cons"!==a[0])a=void 0;else if(a=["Tuple2",a[1],k(a[2])],"Tuple2"!==a[0]||
"Tuple2"!==a[1][0])a=void 0;else var e=a[1][1],b=a[1][2],a="Tuple2"!==a[2][0]?void 0:["Tuple2",["Cons",e,a[2][1]],["Cons",b,a[2][2]]];return a}],b=e.length;b--;){var c=e[b](a);if(void 0!==c){a=c;break a}}a=void 0}return a}function i(a){return function(e){a:{for(var b=[function(a){return"Nil"!==a[0]?void 0:["Nil"]},function(a){if("Cons"===a[0]){var e=a[1];return"Nil"!==a[2][0]?void 0:["Cons",e,["Nil"]]}},function(e){if("Cons"===e[0]){var b=e[1];if("Cons"===e[2][0]){var c=e[2][1],e=e[2][2];return["Cons",
b,["Cons",a,i(a)(["Cons",c,e])]]}}}],c=b.length;c--;){var d=b[c](e);if(void 0!==d){e=d;break a}}e=void 0}return e}}function j(a){return function(e){a:{for(var b=[function(a){return"Nil"!==a[0]?void 0:["Nil"]},function(a){if("Cons"===a[0]){var e=a[1];return"Nil"!==a[2][0]?void 0:e}},function(e){if("Cons"===e[0]){var b=e[1];if("Cons"===e[2][0]){var c=e[2][1],e=e[2][2];return Value.append(b,Value.append(a,j(a)(["Cons",c,e])))}}}],c=b.length;c--;){var d=b[c](e);if(void 0!==d){e=d;break a}}e=void 0}return e}}
var h=function(a){throw"Function '"+a+"' expecting a list!";},m=b(function(a){return function(e){return["Cons",a,e]}})(["Nil"]),l=c(function(a){return function(e){return Value.append(a,e)}})(["Nil"]),o=b(function(a){return function(e){return a&&e}})(!0),p=b(function(a){return function(e){return a||e}})(!1),n=b(function(a){return function(e){return a+e}})(0),q=b(function(a){return function(e){return a*e}})(1),s=a(function(a){return function(e){return Math.max(a,e)}}),r=a(function(a){return function(e){return Math.min(a,
e)}});return{head:function(a){if("Cons"!==a[0])throw"Error: 'head' only accepts lists of length greater than one.";return a[1]},tail:function(a){if("Cons"!==a[0])throw"Error: 'tail' only accepts lists of length greater than one.";return a[2]},last:function(a){if("Cons"!==a[0])throw"Error: 'last' only accepts lists of length greater than one.";for(var e=a[1];"Cons"===a[0];)e=a[1],a=a[2];return e},map:d,foldl:b,foldr:c,foldl1:a,foldr1:function(a){return function(e){if("Nil"===e[0])throw"'foldr1' requires an non-empty list.";
"Cons"!==e[0]&&h("foldr1");for(var b=[];"Cons"===e[0];)b.push(e[1]),e=e[2];for(var e=b.pop(),c=b.length;c--;)e=a(b[c])(e);return e}},scanl:g,scanl1:function(a){return function(e){if("Cons"!==e[0])throw"Error: 'scanl1' requires a list of at least length 1.";return g(a)(e[1])(e[2])}},filter:function(a){return function(e){if("Nil"===e[0])return e;"Cons"!==e[0]&&h("filter");for(var b=[];"Cons"===e[0];)a(e[1])&&b.push(e[1]),e=e[2];for(var e=["Nil"],c=b.length;c--;)e=["Cons",b[c],e];return e}},length:function(a){for(var e=
0;"Cons"===a[0];)e+=1,a=a[2];return e},reverse:m,concat:l,concatMap:function(a){return function(e){return l(d(a)(e))}},and:o,or:p,forall:function(a){return b(function(e){return function(b){return b&&a(e)}})(!0)},exists:function(a){return b(function(e){return function(b){return b||a(e)}})(!1)},sum:n,product:q,maximum:s,minimum:r,partition:f,zipWith:function(a){return function(e){return function(b){if("Nil"===e[0]||"Nil"===b[0])return["Nil"];("Cons"!==e[0]||"Cons"!==b[0])&&h("zipWith");for(var c=[];"Cons"===
e[0]&&"Cons"===b[0];)c.push(a(e[1])(b[1])),e=e[2],b=b[2];for(var b=["Nil"],d=c.length;d--;)b=["Cons",c[d],b];return b}}},zip:function(a){return function(b){if("Nil"===a[0]||"Nil"===b[0])return["Nil"];("Cons"!==a[0]||"Cons"!==b[0])&&h("zip");for(var c=[];"Cons"===a[0]&&"Cons"===b[0];)c.push(["Tuple2",a[1],b[1]]),a=a[2],b=b[2];for(var b=["Nil"],d=c.length;d--;)b=["Cons",c[d],b];return b}},unzip:k,intersperse:i,intercalate:j,sort:function(a){if("Nil"===a[0])return a;"Cons"!==a[0]&&h("sort");for(var b=
[];"Cons"===a[0];)b.push(a[1]),a=a[2];b.sort(function(a,b){return a-b});for(var a=["Nil"],c=b.length;c--;)a=["Cons",b[c],a];return a},take:function(a){return function(b){if(0>=a)return["Nil"];if("Nil"===b[0])return b;"Cons"!==b[0]&&h("take");var c=["Cons",b[1],["Nil"]],d=c,b=b[2];for(--a;"Cons"===b[0]&&0<a;)d[2]=["Cons",b[1],["Nil"]],d=d[2],b=b[2],--a;return c}},drop:function(a){return function(b){if("Nil"===b[0])return b;for("Cons"!==b[0]&&h("drop");"Cons"===b[0]&&0<a;)b=b[2],--a;return b}}}}(),
Data=function(){var d;d=function(b){return function(a){return"Just"===b[0]?["Cons",b[1],a]:a}};var b=function(b){return function(a){return function(d){var f=b(a);return"Just"===f[0]?["Cons",f[1],d]:d}}};d={Just:function(b){return["Just",b]},Nothing:["Nothing"],catMaybes:List.foldr(d)(["Nil"]),isJust:function(b){return"Just"===b[0]},isNothing:function(b){return"Nothing"===b[0]},fromMaybe:function(b){return function(a){return"Just"===a[0]?a[1]:b}},consMaybe:d,mapMaybe:function(c){return List.foldr(b(c))(["Nil"])},
maybe:function(b){return function(a){return function(d){return"Just"===d[0]?a(d[1]):b}}}};return{String:{toText:Value.toText,properEscape:Value.properEscape},Char:{fromCode:function(b){return String.fromCharCode(b)},toCode:function(b){return b.charCodeAt(0)},toUpper:function(b){return b.toUpperCase()},toLower:function(b){return b.toLowerCase()},toLocaleUpper:function(b){return b.toLocaleUpperCase()},toLocaleLower:function(b){return b.toLocaleLowerCase()}},Maybe:d,List:List}}(),Color=function(){var d=
function(b,c,a,d){return{r:b,g:c,b:a,a:d}};return{black:d(0,0,0,1),white:d(255,255,255,1),red:d(255,0,0,1),green:d(0,255,0,1),blue:d(0,0,255,1),gray:d(128,128,128,1),grey:d(128,128,128,1),yellow:d(255,255,0,1),cyan:d(0,255,255,1),magenta:d(255,0,255,1),rgba:function(b){return function(c){return function(a){return function(g){return d(b,c,a,g)}}}},rgb:function(b){return function(c){return function(a){return d(b,c,a,1)}}},Internal:{extract:function(b){return 1===b.a?"rgb("+b.r+","+b.g+","+b.b+")":"rgba("+
b.r+","+b.g+","+b.b+","+b.a+")"}}}}(),Element=function(){var d=function(a){a=document.createElement(a);a.id=Guid.guid();a.style.padding="0";a.style.margin="0";return a},b=function(a){var b=d("div");b.appendChild(a);return b},c=function(a){return function(b){return function(c){var f=d("div");f.isElmLeaf=!0;f.isElmText=!0;f.innerHTML=c;f.style.textAlign=b;0<a&&(f.style.width=a+"px");return f}}},a=c(0)("left"),g=c(0)("justify"),f=c(0)("center"),k=c(0)("right"),i=function(a){return"DIV"===a.tagName?a:
b(a)},j=function(a){a.style.styleFloat="left";a.style.cssFloat="left";return a},h=function(a){a.style.position="absolute";return a},m=function(a,b,c){for(var f=d("div"),h=c.length;h--;){var g=b(c[h]);f.appendChild(g)}f.elmFlowDirection=a;return f},l=function(a){return function(b){for(var c=[];"Cons"===b[0];)c.push(b[1]),b=b[2];3<=a&&c.reverse();b=a%3;if(0==b)return m("Y",i,c);if(1==b)return m("X",j,c);if(2==b)return m("Z",h,c)}},o=function(a){return function(b){if("A"===b.tagName)return o(a)(b.firstChild),
b;if(b.hasOwnProperty("isElmText")){var d=c(a)(b.style.textAlign)(b.innerHTML);b.style.height=d.style.height}b.style.width=a+"px";return b}};return{text:a,image:function(a){var b=d("img");b.isElmLeaf=!0;b.onload=function(){""===b.style.width&&0<this.width&&(b.style.width=b.width=this.width+"px");""===b.style.height&&0<this.height&&(b.style.height=b.height=this.height+"px");Dispatcher.adjust()};b.src=Value.toText(a);b.name=b.src;return b},fittedImage:function(a){return function(b){return function(c){var f=
d("canvas");f.style.width=a+"px";f.style.height=b+"px";f.width=a;f.height=b;f.innerHTML="Your browser does not support the canvas element.";f.isElmLeaf=!0;var h=d("img");h.onload=function(){if(f.getContext){var c=f.getContext("2d"),e=0,d=0,g=this.width,j=this.height;a/b>this.width/this.height?(j=this.width*b/a,d=(this.height-j)/2):(g=this.height*a/b,e=(this.width-g)/2);c.drawImage(h,e,d,g,j,0,0,f.width,f.height)}};h.src=Value.toText(c);return f}}},video:function(a){var a=Value.toText(a),b=d("video");
b.controls="controls";var c=d("source");c.src=a;c.type="video/"+a.substring(a.length-3,a.length);b.appendChild(c);b.isElmLeaf=!0;return b},audio:function(a){var a=Value.toText(a),b=d("video");b.controls="controls";var c=d("source");c.src=a;c.type="audio/"+a.substring(a.length-3,a.length);b.appendChild(c);b.isElmLeaf=!0;return b},collage:function(a){return function(b){return function(c){var f=d("canvas");f.style.width=a+"px";f.style.height=b+"px";f.width=a;f.height=b;if(f.getContext){var h=f.getContext("2d");
for(h.clearRect(0,0,f.width,f.height);"Cons"===c[0];)h=c[1](h),c=c[2];return f}f.innerHTML="Your browser does not support the canvas element.";f.isElmLeaf=!0;return f}}},flow:l,layers:l(2),rectangle:function(a){return function(b){var c=d("div");c.isElmLeaf=!0;c.style.width=a+"px";c.style.height=b+"px";return c}},beside:function(a){return function(b){return l(4)(["Cons",a,["Cons",b,["Nil"]]])}},above:function(a){return function(b){return l(3)(["Cons",a,["Cons",b,["Nil"]]])}},below:function(a){return function(b){return l(0)(["Cons",
a,["Cons",b,["Nil"]]])}},box:function(a){return function(b){b.style.position="absolute";b.style.margin="auto";var c=(a-1)%3,f=(a-1)/3;2>c&&(b.style.left=0);0<c&&(b.style.right=0);2>f&&(b.style.top=0);0<f&&(b.style.bottom=0);c=d("div");c.style.position="relative";c.appendChild(b);return c}},width:o,height:function(a){return function(b){("A"===b.tagName?b.firstChild:b).style.height=a+"px";return b}},size:function(a){return function(b){return function(c){var d="A"===c.tagName?c.firstChild:c;d.style.width=
a+"px";d.style.height=b+"px";return c}}},color:function(a){return function(b){b.style.backgroundColor=Color.Internal.extract(a);return b}},opacity:function(a){return function(b){b.style.opacity=a;return b}},link:function(a){return function(c){var f=d("a");f.href=Text.fromString(a);f.appendChild(c);return b(f)}},asText:function(a){return c(0)("left")(Value.show(a))},plainText:function(a){return c(0)("left")(Value.toText(a))},justifiedText:g,centeredText:f,rightedText:k,up:0,left:1,inward:2,down:3,
right:4,outward:5,correctTextSize:function(a){var b=a.style.width?a.style.width.slice(0,-2):0,c=d("div");c.innerHTML=a.innerHTML;c.style.textAlign=a.style.textAlign;0<b&&(c.style.width=b+"px");c.style.visibility="hidden";c.style.styleFloat="left";c.style.cssFloat="left";document.body.appendChild(c);var f=window.getComputedStyle(c);0>=b&&(a.style.width=f.getPropertyValue("width"));a.style.height=f.getPropertyValue("height");document.body.removeChild(c)},jsElement:function(a){return function(b){return function(c){var f=
d("div");f.isElmLeaf=!0;f.style.width=a+"px";f.style.height=b+"px";f.appendChild(c);return f}}}}}(),Text=function(){function d(a){return Value.toText(a)}var b=function(a){return function(b){return"<"+a+' style="padding:0;margin:0">'+b+"</"+a+">"}},c=function(a,b){return function(c){return"<span style='"+a+":"+b+"'>"+c+"</span>"}},a=function(a){return c("font-family",a)},g=b("h1"),f=c("font-style","italic"),b=b("b"),k=c("text-decoration","underline"),i=c("text-decoration","overline"),j=c("text-decoration",
"line-through");return{fromString:d,toText:d,header:g,height:function(a){return c("font-size",a+"em")},italic:f,bold:b,underline:k,overline:i,strikeThrough:j,monospace:a("monospace"),typeface:a,color:function(a){return c("color",Color.Internal.extract(a))},link:function(a){return function(b){return"<a href='"+d(a)+"'>"+b+"</a>"}}}}(),Shape=function(){var d=function(b,a,d,f){return{center:b,points:a,theta:d,scale:f}},b=function(b){return function(a){return function(d){return function(f){f.save();f.translate(d.center[0],
d.center[1]);f.rotate(d.theta);f.scale(d.scale,d.scale);f.beginPath();var k=d.points;f.moveTo(k[0][0],k[0][1]);for(var i=k.length;i--;)f.lineTo(k[i][0],k[i][1]);f.closePath();b?(f.fillStyle=Color.Internal.extract(a),f.fill()):(f.strokeStyle=Color.Internal.extract(a),f.stroke());f.restore();return f}}}};return{polygon:function(b){return function(a){for(var g=[];"Cons"===b[0];)g.push([b[1][1],b[1][2]]),b=b[2];a=[a[1],a[2]];return d(a,g,0,1)}},ngon:function(b){return function(a){return function(g){for(var f=
[],k=b;k--;)f.push([a*Math.cos(2*Math.PI*k/b),a*Math.sin(2*Math.PI*k/b)]);g=[g[1],g[2]];return d(g,f,0,1)}}},rect:function(b){return function(a){return function(g){var f=[[-b/2,-a/2],[b/2,-a/2],[b/2,a/2],[-b/2,a/2]],g=[g[1],g[2]];return d(g,f,0,1)}}},oval:function(b){return function(a){return function(g){for(var f=[],k=2*Math.PI;0<k;k-=Math.PI/50)f.push([b/2*Math.cos(k),a/2*Math.sin(k)]);g=[g[1],g[2]];return d(g,f,0,1)}}},move:function(b){return function(a){return function(g){return d([b+g.center[0],
a+g.center[1]],g.points,g.theta,g.scale)}}},rotate:function(b){return function(a){return d(a.center,a.points,a.theta+2*Math.PI*b,a.scale)}},scale:function(b){return function(a){return d(a.center,a.points,a.theta,a.scale*b)}},filled:b(!0),outlined:b(!1),customOutline:function(b){return function(a){return function(d){d.points.push(d.points[0]);return Line.customLine(b)(a)(d)}}}}}(),Line=function(){var d=function(b){return function(c){return function(a){if("string"===typeof b[0]){for(var d=[];"Cons"===
b[0];)d.push(b[1]),b=b[2];b=d}0===b.length&&(b=[8,4]);return function(d){d.save();d.beginPath();d.translate(a.center[0],a.center[1]);d.rotate(a.theta);d.scale(a.scale,a.scale);var g=b,i=a.points,j=i.length-1,h=i[j][0],m=i[j][1],l=0,o=0,p=0,n=0,q=0,s=0,r=g.length,t=!0,e=g[0];for(d.moveTo(h,m);j--;){l=i[j][0];o=i[j][1];p=l-h;n=o-m;for(q=Math.sqrt(p*p+n*n);e<=q;)h+=p*e/q,m+=n*e/q,d[t?"lineTo":"moveTo"](h,m),p=l-h,n=o-m,q=Math.sqrt(p*p+n*n),t=!t,s=(s+1)%r,e=g[s];0<q&&(d[t?"lineTo":"moveTo"](l,o),e-=q);
h=l;m=o}d.strokeStyle=Color.Internal.extract(c);d.stroke();d.restore();return d}}}};return{line:function(b){for(var c=[];"Cons"===b[0];)c.push([b[1][1],b[1][2]]),b=b[2];return{center:[0,0],points:c,theta:0,scale:1}},customLine:d,solid:function(b){return function(c){return function(a){a.save();a.beginPath();a.translate(c.center[0],c.center[1]);a.rotate(c.theta);a.scale(c.scale,c.scale);var d=c.points,f=d.length;for(a.moveTo(d[f-1][0],d[f-1][1]);f--;)a.lineTo(d[f][0],d[f][1]);a.strokeStyle=Color.Internal.extract(b);
a.stroke();a.restore();return a}}},dashed:d([8,4]),dotted:d([3,3])}}(),Elm=function(){var d=function(a,b,c){for(var d=a.kids,f=d.length;f--;)d[f].recv(b,c,a.id)},b=function(a){this.id=Guid.guid();this.value=a;this.kids=[];this.recv=function(a,b,c){if(b=b===this.id)this.value=c;d(this,a,b)};Dispatcher.inputs.push(this)},c=function(a,b){this.id=Guid.guid();this.value=null;this.kids=[];this.inbox={};b.reverse();this.recalc=function(){for(var c=a,d=b.length;d--;)c=c(b[d].value);this.value=c};this.recalc();
this.recv=function(a,c){this.inbox.hasOwnProperty(a)||(this.inbox[a]={changed:!1,count:0});var f=this.inbox[a];f.count+=1;c&&(f.changed=!0);f.count==b.length&&(f.changed&&this.recalc(),d(this,a,f.changed),delete this.inbox[a])};for(var c=b.length;c--;)b[c].kids.push(this)},a=function(a,b,c){this.id=Guid.guid();this.value=b;this.kids=[];this.recv=function(b,f){f&&(this.value=a(c.value)(this.value));d(this,b,f)};c.kids.push(this)},g=function(a,b,c){this.id=Guid.guid();this.value=a(c.value)?b:c.value;
this.kids=[];this.recv=function(b,f){var g=f&&!a(c.value);g&&(this.value=c.value);d(this,b,g)};c.kids.push(this)},f=function(a){this.id=Guid.guid();this.value=a.value;this.kids=[];this.recv=function(b,c){var f=c&&!eq(this.value,a.value);f&&(this.value=a.value);d(this,b,f)};a.kids.push(this)},k=function(a){return function(b){return function(d){d=new c(function(a){return function(b){return[a,b]}},[a,d]);d=new g(function(a){return a[0]},[!0,b],d);return new c(function(a){return a[1]},[d])}}},i=function(a,
b){this.id=Guid.guid();this.value=b.value;this.kids=[];this.inbox={};this.recv=function(c,f,g){if(f=f&&g===a.id)this.value=b.value;d(this,c,f)};a.kids.push(this);b.kids.push(this)};return{Input:function(a){return new b(a)},Lift:function(a,b){return new c(a,b)},Fold:function(b,c,d){return new a(b,c,d)},keepIf:function(a){return function(b){return function(c){return new g(function(b){return!a(b)},b,c)}}},dropIf:function(a){return function(b){return function(c){return new g(a,b,c)}}},keepWhen:function(a){return k(new c(function(a){return!a},
[a]))},dropWhen:k,dropRepeats:function(a){return new f(a)},sampleOn:function(a){return function(b){return new i(a,b)}}}}(),Dispatcher=function(){var d=null,b=0,c=[],a=function(b){var c=b.childNodes,d=c.length;if(b.hasOwnProperty("isElmLeaf")){b.hasOwnProperty("isElmText")&&Element.correctTextSize(b);var c=""===b.style.width?0:b.style.width.slice(0,-2)-0,g=""===b.style.height?0:b.style.height.slice(0,-2)-0;return[c,g]}if(1===d){var h=a(c[0]);b.style.hasOwnProperty("width")&&0<b.style.width.length&&
(h[0]=b.style.width.slice(0,-2)-0);b.style.hasOwnProperty("height")&&0<b.style.height.length&&(h[1]=b.style.height.slice(0,-2)-0);0!==h[0]&&(b.style.width=h[0]+"px");0!==h[1]&&(b.style.height=h[1]+"px");return h}for(var m=0,l=g=0,o=0,p=!0,n=!0;d--;)h=a(c[d]),m=Math.max(m,h[0]),g=Math.max(g,h[1]),l+=h[0],o+=h[1],p=p&&0<h[0],n=n&&0<h[1];c=m;d=b.elmFlowDirection;"X"===d&&(c=p?l:0);"Y"===d&&(g=n?o:0);0<c&&(b.style.width=c+"px");0<g&&(b.style.height=g+"px");return[c,g]},g=function(){var b=document.getElementById("content");
a(b.children[0])};return{initialize:function(){d=ElmCode.main();d.hasOwnProperty("recv")||(d=Elm.Input(d));document.getElementById("content").appendChild(d.value);g();var a=document.getElementById("widthChecker").offsetWidth;a!==window.innerWidth&&Dispatcher.notify(Window.dimensions.id,Value.Tuple(a,window.innerHeight));d=Elm.Lift(function(a){var b=document.getElementById("content"),c=b.children[0];b.replaceChild(a,c);delete c;g();return a},[d])},notify:function(a,d){b+=1;for(var g=c.length;g--;)c[g].recv(b,
a,d)},adjust:g,inputs:c}}(),Signal=function(){function d(a){for(var b=["Nil"],c=a.length;c--;)b=["Cons",a[c],b];return b}var b;b=document.addEventListener?function(a,b,c){a.addEventListener(b,c,!1)}:function(a,b,c){a.attachEvent("on"+b,c)};var c,a=function(a){var b=0,c=0;a||(a=window.event);if(a.pageX||a.pageY)b=a.pageX,c=a.pageY;else if(a.clientX||a.clientY)b=a.clientX+document.body.scrollLeft+document.documentElement.scrollLeft,c=a.clientY+document.body.scrollTop+document.documentElement.scrollTop;
return Value.Tuple(b,c)},g=Elm.Input(Value.Tuple(0,0)),f=Elm.Input(!1),k=Elm.Input(!1),i=Elm.Input(Value.Tuple());b(document,"click",function(){Dispatcher.notify(k.id,!0);Dispatcher.notify(i.id,Value.Tuple());Dispatcher.notify(k.id,!1)});b(document,"mousedown",function(){Dispatcher.notify(f.id,!0)});b(document,"mouseup",function(){Dispatcher.notify(f.id,!1)});b(document,"mousemove",function(b){Dispatcher.notify(g.id,a(b))});c={position:g,x:Elm.Lift(function(a){return a[1]},[g]),y:Elm.Lift(function(a){return a[2]},
[g]),isClicked:k,isDown:f,clicks:i,isClickedOn:function(a){var c=Elm.Input(!1);b(a,"click",function(){Dispatcher.notify(c.id,!0);Dispatcher.notify(c.id,!1)});return Value.Tuple(a,c)}};var j,h=Elm.Input(Value.Tuple(window.innerWidth,window.innerHeight));b(window,"resize",function(){var a=document.getElementById("widthChecker").offsetWidth;Dispatcher.notify(h.id,Value.Tuple(a,window.innerHeight))});j={dimensions:h,width:Elm.Lift(function(a){return a[1]},[h]),height:Elm.Lift(function(a){return a[2]},
[h])};var m=function(a,b){return"Nil"===b[0]?b:b[1]===a?b[2]:["Cons",b[1],m(a,b[2])]},l=Elm.Input(["Nil"]),o=Elm.Input(["Nothing"]);b(document,"keydown",function(a){var b;a:{for(b=l.value;"Nil"!==b[0];){if(b[1]===a.keyCode){b=!0;break a}b=b[2]}b=!1}b||Dispatcher.notify(l.id,["Cons",a.keyCode,l.value])});b(document,"keyup",function(a){a=m(a.keyCode,l.value);Dispatcher.notify(l.id,a)});b(window,"blur",function(){Dispatcher.notify(l.id,["Nil"])});b(document,"keypress",function(a){Dispatcher.notify(o.id,
["Just",a.charCode||a.keyCode]);Dispatcher.notify(o.id,["Nothing"])});var p={Raw:{keysDown:l,charPressed:o}},n;n=function(a){return function(b){var c=Elm.Input(["Waiting"]),f={};window.XMLHttpRequest?f=new XMLHttpRequest:window.ActiveXObject&&(f=new ActiveXObject("Microsoft.XMLHTTP"));f.onreadystatechange=function(){4===f.readyState&&Dispatcher.notify(c.id,200===f.status?["Success",d(f.responseText)]:["Failure",f.status,d(f.statusText)])};f.open(a,Value.toText(b),!0);f.send(null);return c}};var q=
function(a){return function(b){var c=Elm.Input(["Nothing"]),b=Elm.Lift(function(b){if("Just"!==b[0]){try{Dispatcher.notify(c.id,["Nothing"])}catch(f){}return[]}try{Dispatcher.notify(c.id,["Just",["Waiting"]])}catch(g){c.value=["Just",["Waiting"]]}var h={};window.XMLHttpRequest?h=new XMLHttpRequest:window.ActiveXObject&&(h=new ActiveXObject("Microsoft.XMLHTTP"));h.onreadystatechange=function(){4===h.readyState&&Dispatcher.notify(c.id,["Just",200===h.status?["Success",d(h.responseText)]:["Failure",
h.status,d(h.statusText)]])};h.open(a,Value.toText(b[1]),!0);h.send(null);return[]},[b]);return Elm.Lift(function(a){return function(){return a}},[c,b])}};n={get:n("GET"),post:n("POST"),gets:q("GET"),posts:q("POST")};var s=function(a){a.isElmLeaf=!0;var c=Elm.Input(["Nil"]);b(a,"keyup",function(){Dispatcher.notify(c.id,d(a.value));a.focus()});return Value.Tuple(a,c)},r=function(a){a=document.createElement(a);a.id=Guid.guid();return a},t=function(a){for(var c=r("select"),d=[];"Cons"===a[0];){var f=
r("option"),g=Text.toText(a[1][1]);f.value=g;f.innerHTML=g;c.appendChild(f);d.push(a[1][2]);a=a[2]}var h=Elm.Input(d[0]);b(c,"change",function(){Dispatcher.notify(h.id,d[c.selectedIndex])});return Value.Tuple(c,h)};return{addListener:b,Mouse:c,Keyboard:p,Time:{every:function(a){var a=1E3*a,b=Elm.Input(0),c=0;setInterval(function(){c+=a;Dispatcher.notify(b.id,c/1E3)},a);return b},after:function(a){var a=1E3*a,b=Elm.Input(!1);setTimeout(function(){Dispatcher.notify(b.id,!0)},a);return b},before:function(a){var a=
1E3*a,b=Elm.Input(!0);setTimeout(function(){Dispatcher.notify(b.id,!1)},a);return b}},Window:j,HTTP:n,Random:{inRange:function(a){return function(b){return Elm.Input(Math.floor(Math.random()*(b-a+1))+a)}},randomize:function(a){return function(b){return function(c){return Elm.Lift(function(){return Math.floor(Math.random()*(b-a+1))+a},[c])}}}},Input:{textArea:function(a){return function(b){var c=r("textarea");c.rows=b;c.cols=a;return s(c,"")}},textField:function(a){var b=r("input");b.type="text";return s(b,
a)},password:function(a){var b=r("input");b.type="password";return s(b,a)},checkbox:function(a){var c=r("input");c.type="checkbox";c.checked=a;var d=Elm.Input(a);b(c,"change",function(){Dispatcher.notify(d.id,c.checked)});return Value.Tuple(c,d)},dropDown:t,stringDropDown:function(a){return t(List.map(function(a){return Value.Tuple(a,a)})(a))},button:function(a){var c=r("input");c.type="button";c.value=Foreign.JavaScript.castStringToJSString(a);var d=Elm.Input(!1);b(c,"click",function(){Dispatcher.notify(d.id,
!0);Dispatcher.notify(d.id,!1)});return Value.Tuple(c,d)}},constant:function(a){return Elm.Input(a)},lift:function(a){return function(b){return Elm.Lift(a,[b])}},lift2:function(a){return function(b){return function(c){return Elm.Lift(a,[b,c])}}},lift3:function(a){return function(b){return function(c){return function(d){return Elm.Lift(a,[b,c,d])}}}},lift4:function(a){return function(b){return function(c){return function(d){return function(f){return Elm.Lift(a,[b,c,d,f])}}}}},foldp:function(a){return function(b){return function(c){return Elm.Fold(a,
b,c)}}},count:function(a){return Elm.Fold(function(){return function(a){return a+1}},0,a)},keepIf:Elm.keepIf,dropIf:Elm.dropIf,keepWhen:Elm.keepWhen,dropWhen:Elm.dropWhen,dropRepeats:Elm.dropRepeats,sampleOn:Elm.sampleOn}}(),Prelude=function(){var d=function(b){return function(c){var a=b%c,a=0==b?0:0<c?0<=b?a:a+c:-d(-b)(-c);return a==c?0:a}};return{id:function(b){return b},not:function(b){return!b},fst:function(b){return b[1]},snd:function(b){return b[2]},rem:function(b){return function(c){return b%
c}},div:function(b){return function(c){return~~(b/c)}},compare:function(b){return function(c){b="object"===typeof b?toText(b):b;c="object"===typeof c?toText(c):c;return[b===c?"EQ":b<c?"LT":"GT"]}},toFloat:function(b){return b},round:function(b){return Math.round(b)},floor:function(b){return Math.floor(b)},ceiling:function(b){return Math.ceil(b)},truncate:function(b){return~~b},sqrt:Math.sqrt,abs:Math.abs,pi:Math.PI,e:Math.E,sin:Math.sin,cos:Math.cos,tan:Math.tan,asin:Math.asin,acos:Math.acos,atan:Math.atan,
mod:d,min:function(b){return function(c){return Math.min(b,c)}},max:function(b){return function(c){return Math.max(b,c)}},flip:function(b){return function(c){return function(a){return b(a)(c)}}},clamp:function(b){return function(c){return function(a){return Math.min(c,Math.max(b,a))}}},curry:function(b){return function(c){return function(a){return b(["Tuple2",c,a])}}},uncurry:function(b){return function(c){if("Tuple2"!==c[0])throw"Function was uncurry'd but was not given a pair.";return b(c[1])(c[2])}},
logBase:function(b){return function(c){return Math.log(c)/Math.log(b)}},Just:Data.Maybe.Just,Nothing:Data.Maybe.Nothing,maybe:Data.Maybe.maybe,map:Data.List.map,filter:Data.List.filter,head:Data.List.head,tail:Data.List.tail,last:Data.List.last,length:Data.List.length,reverse:Data.List.reverse,foldr:Data.List.foldr,foldr1:Data.List.foldr1,foldl:Data.List.foldl,foldl1:Data.List.foldl1,and:Data.List.and,or:Data.List.or,forall:Data.List.forall,exists:Data.List.exists,sum:Data.List.sum,product:Data.List.product,
concat:Data.List.concat,concatMap:Data.List.concatMap,maximum:Data.List.maximum,minimum:Data.List.minimum,scanl:Data.List.scanl,scanl1:Data.List.scanl1,take:Data.List.take,drop:Data.List.drop,lift:Signal.lift,lift2:Signal.lift2,lift3:Signal.lift3,lift4:Signal.lift4,foldp:Signal.foldp,constant:Signal.constant,count:Signal.count,keepIf:Signal.keepIf,dropIf:Signal.dropIf,keepWhen:Signal.keepWhen,dropWhen:Signal.dropWhen,dropRepeats:Signal.dropRepeats,sampleOn:Signal.sampleOn}}(),eq=Value.eq;
Signal.addListener(document,"elm_log",function(d){console.log(d.value)});Signal.addListener(document,"elm_title",function(d){document.title=d.value});Signal.addListener(document,"elm_redirect",function(d){0<d.value.length&&(window.location=d.value)});var includeGlobal=this;
(function(){var d=function(b){for(var a in b)if("Internal"!==a)try{includeGlobal[a]=b[a]}catch(d){"length"===a&&(includeGlobal.execScript("var length;"),length=b[a])}},b=function(b){return function(a){includeGlobal[b]=includeGlobal[b]||{};for(var d in a)"Internal"!==d&&(includeGlobal[b][d]=a[d])}};d(Element);d(Text);color=Element.color;height=Element.height;show=Value.show;d(Color);d(Shape);d(Line);b("Time")(Signal.Time);b("Mouse")(Signal.Mouse);b("Keyboard")(Signal.Keyboard);b("Window")(Signal.Window);
b("HTTP")(Signal.HTTP);b("Input")(Signal.Input);b("Random")(Signal.Random)})();var ElmCode={};ElmCode.Data=Data;ElmCode.Signal=Signal;ElmCode.Data.List=List;ElmCode.Foreign=Foreign;ElmCode.Prelude=Prelude;