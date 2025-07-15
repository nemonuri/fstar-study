// For more information see http://www.fstar-lang.org/tutorial/
module Part4.Pure.Factorial

open FStar.Mul
let rec factorial (x:int)
  : Pure int (requires x >= 0) (ensures fun r -> r >= 1)
  = if x = 0
    then 1
    else x * factorial (x - 1)