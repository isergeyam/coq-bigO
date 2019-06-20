let rec length l =
  match l with
  | [] -> 0
  | _ :: l -> 1 + length l

let length2 l = length l + length l

let rec loop l =
  match l with
  | [] -> 0
  | _ :: l' -> length l + loop l'
