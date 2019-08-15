let bellman_ford (inf : int) source (edges : (int * int * int) array) (nb_nodes : int) =
  let d = Array.make nb_nodes inf in
  d.(source) <- 0;
  for i = 0 to nb_nodes - 2 do
    for j = 0 to Array.length edges - 1 do
      let (v1, v2, w) = edges.(j) in
      d.(v2) <- min d.(v2) (d.(v1) + w)
    done
  done;
  d
