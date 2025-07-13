module Part2.STInt

let st a = int -> a & int

let read_and_increment_v0
  : st int
  = fun s0 -> s0, s0 + 1

let inc_twice_v0
  : st int
  = fun s0 ->
      let x, s1 = read_and_increment_v0 s0 in
      let _, s2 = read_and_increment_v0 s1 in
      x, s2


let read
  : st int
  = fun s -> s, s

let write (s1:int)
  : st unit
  = fun _ -> (), s1

let bind #a #b
         (f: st a)
         (g: a -> st b)
  : st b
  = fun s0 ->
      let x, s1 = f s0 in
      g x s1

let return #a (x:a)
  : st a
  = fun s -> x, s

let read_and_increment_v1 : st int = 
  bind read (fun x -> 
  bind (write (x + 1)) (fun _ -> 
  return x))

let (let!) = bind

let read_and_increment : st int =
  let! x = read in
  write (x + 1) ;!
  return x


