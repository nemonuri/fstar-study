// For more information see http://www.fstar-lang.org/tutorial/
module Program

open FStar.IO
open FStar.Int
open FStar.UInt32

let naturalNumber = x:int{x >= 0}

let number1:naturalNumber = 1
let number2 = to_int_t 32 number1
let number3 = to_uint number2
let number4:UInt32.t = uint_to_t number3

let main = print_uint32 number4
