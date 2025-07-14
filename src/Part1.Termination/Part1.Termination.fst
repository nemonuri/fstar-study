// For more information see http://www.fstar-lang.org/tutorial/
module Part1.Termination

let rec ackermann (m n:nat)
  : Tot nat (decreases %[m;n])
  = if m=0 then n + 1
    else if n = 0 then ackermann (m - 1) 1
    else ackermann (m - 1) (ackermann m (n - 1))