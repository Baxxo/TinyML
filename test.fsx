//let test1 f g h = (f g) g (f h)

//let f x y z = z (y x) in f

//let rec g x y z = g (z (y x)) in g

//let tupint = (1, 2, 3) in tupint

//let tupstr = ("a","b","c") in tupstr

//let tupmix = (1,"b",2.3) in tupmix

//let a = a in let b = b in let c = c in let tuplepoli = (a,b,c) in tuplepoli

//let rec g x y z = g (z (y x)) in g

let id x = x
(id 7, id true, id "str")

// non funziona, capire perché