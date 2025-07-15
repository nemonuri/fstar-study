module Part4.Ghost.Factorial
open FStar.Mul

let rec factorial (n:nat)
  : GTot nat
  = if n = 0 then 1 else n * factorial (n - 1)

let rec factorial_tail (n:nat) (out:nat)
  : Tot (r:nat { r == out * factorial n })
  = if n = 0 then out
    else factorial_tail (n - 1) (n * out)

let fact (n:nat) 
  : Tot (r:nat { r == factorial n })
  = factorial_tail n 1

[@@expect_failure]
let factorial_bad (n:nat) (out:nat)
  : Tot (r:nat { r == out * factorial n }) // Ghost 함수를 Specification 에 사용하는 건 됨
  = out * factorial n // Ghost 함수를 실제 출력에 사용하는 건 안됨