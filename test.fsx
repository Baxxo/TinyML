let rec fatt num = if num <= 0 then 1 else num * fattoriale (num - 1) in 3

let rec fact num = if num = 1 then 1 else num * fact (num - 1) in fact 3