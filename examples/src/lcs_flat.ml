(* O(n*m) *)
let lcs (a : int array) (b : int array) : int array =
  let n = Array.length a in
  let m = Array.length b in
  let c = Array.make ((n+1)*(m+1)) [] in
  for i = 1 to n do
    for j = 1 to m do
      if a.(i-1) = b.(j-1)
      then c.(i*(m+1) + j) <- List.append c.((i-1)*(m+1) + j - 1) [a.(i-1)]
      else if List.length c.((i-1)*(m+1) + j) > List.length c.(i*(m+1) + j - 1)
        then c.(i*(m+1) + j) <- c.((i-1)*(m+1) + j)
        else c.(i*(m+1) + j) <- c.(i*(m+1) + j - 1)
        (* c.(i).(j) <- if List.length c.(i-1).(j) > List.length c.(i).(j-1) then c.(i-1).(j) else c.(i).(j-1) *)
      (* longest c.(i-1).(j) c.(i).(j-1) *)
      done
    done; 
  Array.of_list c.((n+1)*(m+1)-1);;

(* lcs (Array.of_list [1;2;3;4;5;3;2;1]) (Array.of_list [1;33;2;1]) ;;

lcs (Array.of_list [1;1;1;1]) (Array.of_list [1;3;5;1;4;3;5;6;1]) ;;

lcs (Array.of_list [1;2;3;5]) (Array.of_list [1;3;5;1;4;3;5;6;1]) ;; *)