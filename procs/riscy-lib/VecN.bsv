
// bsvtokami does not yet support typeclasses, so use these instead of BuildVector::*

import Vector::*;

function Vector#(1, element_t) vec1(element_t v0);
   return cons(v0, nil);
endfunction
function Vector#(2, element_t) vec2(element_t v0, element_t v1);
   return cons(v1, cons(v0, nil));
endfunction
function Vector#(3, element_t) vec3(element_t v0, element_t v1, element_t v2);
   return cons(v2, cons(v1, cons(v0, nil)));
endfunction
function Vector#(4, element_t) vec4(element_t v0, element_t v1, element_t v2, element_t v3);
   return cons(v3, cons(v2, cons(v1, cons(v0, nil))));
endfunction
function Vector#(5, element_t) vec5(element_t v0, element_t v1, element_t v2, element_t v3, element_t v4);
   return cons(v4, cons(v3, cons(v2, cons(v1, cons(v0, nil)))));
endfunction
function Vector#(6, element_t) vec6(element_t v0, element_t v1, element_t v2, element_t v3, element_t v4, element_t v5);
   return cons(v5, cons(v4, cons(v3, cons(v2, cons(v1, cons(v0, nil))))));
endfunction
