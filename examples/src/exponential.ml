let rec f n =
  if n = 0 then ()
  else begin
    f (n-1);
    f (n-1)
  end

let loop n =
  for i = 0 to n-1 do
    f i
  done
