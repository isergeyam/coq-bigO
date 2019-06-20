

(****************************************************)
(* Binary search *)

(* O(log n) *)

let binary_search i j =
  if j-i = 1 then () else
  let m = (i+j)/2 in
  binary_search m j


(****************************************************)
(* Floyd-Warshall *)

(* O(n^3) *)

let floyd_warshall n =
  for i = 0 to n-1 do
    for j = 0 to n-1 do
       for k = 0 to n-1 do
          ()
       done
    done
 done



(****************************************************)
(* Enumerate edges of graph, node by node *)

(* let n = nb_nodes G
   let m = nb_edges G

   t ~> adjacency_list G

   derive:
      n = length t
      m = sum_i t[i]

   code below is O(n+m)
*)

let enum_edges t =
  for i = 0 to pred (Array.length t) do
     List.iter (fun j -> ()) t.(i)
  done
