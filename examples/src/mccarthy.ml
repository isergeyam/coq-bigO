let rec mc n =
  if n > 100 then n - 10
  else mc (mc (n + 11))

let rec mcfuel fuel n =
  if fuel = 0 then -1 (* dummy *)
  else begin
    if n > 100 then n - 10
    else mcfuel (fuel - 1) (mcfuel (fuel - 1) (n + 11))
  end
