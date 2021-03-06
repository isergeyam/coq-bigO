let tick () =
  ()

let rand n =
  0

let tick3 () =
  tick ();
  tick ();
  tick ()

let tick31 () =
  tick ();
  tick3 ()

let loop1 n =
  for i = 0 to n - 1 do
    tick (); tick ()
  done

let let1 n =
  let m = tick (); n + 1 in
  loop1 m

let let2 n =
  let m = rand n in
  loop1 m

let loop2 n =
  let a = rand n in
  let b = rand n in
  for i = a to (a + b) - 1 do
    tick ()
  done

let if1 n cond =
  let a = rand n in
  let b = rand n in
  if cond then loop1 a else loop1 b

let looploop n =
  for i = 0 to n - 1 do
    for j = 0 to i - 1 do
      tick ()
    done
  done

let rec rec1 n =
  if n <= 0 then ()
  else rec1 (n-1)

let rec quick n =
  if n = 0 then ()
  else (
    loop1 n;
    let2 n;
    quick (n - 1)
  )

let rec walk (a: int array) (i: int): int =
  if a.(i) <> 0 && i < Array.length a - 1 then
    walk a (i+1)
  else
    i+1

let full_walk (a: int array) =
  let j = ref 0 in
  while !j < Array.length a do
    j := walk a !j
  done
