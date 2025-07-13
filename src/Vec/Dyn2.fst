module Dyn2

noeq
type dyn =
  | Bool : bool -> dyn
  | Int  : int -> dyn
  | Function : dyn -> dyn -> dyn
  | Function2 : (int -> dyn) -> dyn
  | Identity : dyn -> dyn

#push-options "--__no_positivity"
noeq
type dyn2 =
  | Error1 : (dyn2 -> bool) -> dyn2
  | Error2 : (bool -> dyn2 -> int) -> dyn2
#pop-options