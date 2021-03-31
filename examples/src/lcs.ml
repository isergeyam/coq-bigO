(* O(n*m) *)
let lcs (a : int array) (b : int array) : int array =
  let n = Array.length a in
  let m = Array.length b in
  let c = Array.make (n+1) (Array.make (m + 1) []) in
  for i = 1 to n do
    for j = 1 to m do
      if a.(i-1) = b.(j-1)
      then c.(i).(j) <- List.append c.(i-1).(j-1) [a.(i-1)]
      else c.(i).(j) <- if List.length c.(i-1).(j) > List.length c.(i).(j-1) then c.(i-1).(j) else c.(i).(j-1)
      done
    done; 
  Array.of_list c.(n).(m);;

lcs (Array.of_list [1;2;3;4;5;3;2;1]) (Array.of_list [1;3;2;1]) 