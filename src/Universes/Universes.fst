// For more information see http://www.fstar-lang.org/tutorial/
module Universes

#push-options "--print_universes --print_implicits"

let ty : Type = Type

let ty0 : Type u#1 = Type u#0
let ty0' : Type u#1 = Type0
let ty1 : Type u#2 = Type u#1
let ty2 : Type u#3 = Type u#2

let ty_poly : Type u#(a + 1) = Type u#a

let assert_example1 = assert (ty_poly u#0 == ty0)
let assert_example2 = assert (ty_poly u#1 == ty1)
let assert_example3 = assert (ty_poly u#2 == ty2)
let assert_example4 = assert (ty_poly == ty0)

let nat_type_is_type_of_type0 : Type0 = nat
let bool_type_is_type_of_type0 : Type0 = bool
let nat_to_bool_type_is_type_of_type0 : Type0 = nat -> bool

let id_t : Type u#(i + 1) = a:Type u#i -> a -> a
let id : id_t = fun a x -> x

let seemingly_self_application : id_t = id _ id
let stratified_application : id_t u#i = id u#(i + 1) (id_t u#i) (id u#i)

#pop-options