// For more information see http://www.fstar-lang.org/tutorial/
module Part1.Lemmas
open FStar.Mul

let rec factorial (n:nat)
  : nat
  = if n = 0 then 1
    else n * factorial (n - 1)

(* undeciable *)
// let without_lemma = assert (forall (x:nat). x > 2 ==> factorial x > 2)

let rec factorial_is_greater_than_arg (x:int)
  : Lemma (requires x > 2)
          (ensures factorial x > x)
          (decreases x)
  = if x = 3 then
      ()
    else
      factorial_is_greater_than_arg (x - 1)
      
let with_lemma = assert ( forall (x:int{x > 2}) . ( factorial_is_greater_than_arg x; True ) )