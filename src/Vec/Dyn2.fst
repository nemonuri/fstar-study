module Dyn2

noeq
type dyn =
  | Bool : b:bool -> dyn
  | Int  : i:int -> dyn
  | Function : f1:dyn -> f2:dyn -> dyn