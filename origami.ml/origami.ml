(* Autor: Kamil Poniewierski, 394697 *)


(* Deklaracje Typow *)

(* Punkt na plaszczyznie *)
type point = float * float

(* Poskladana kartka: ile razy kartke przebije szpilka wbita w danym punkcie *)
type kartka = point -> int


(* Funkcje Pomocnicze *)

(* podnosi liczbe do kwadratu *)
let square a =
    a *. a

(* liczy odleglosc miedzy dwoma punktami *)
let dst (x1, y1) (x2, y2) =
    sqrt ( (square (x1 -. x2)) +. (square (y1 -. y2)) )

(* liczy wyznacznik *)
let det (x1, y1) (x2, y2) (x3, y3) =
    x1 *. y2 +. x2 *. y3 +. x3 *. y1 -.
    (x3 *. y2 +. x2 *. y1 +. x1 *. y3)

(* sprawdza czy punkt jest po prawej stronie *)
let is_on_right (x, y) (x1, y1) (x2, y2) =
    det (x1, y1) (x2, y2) (x, y) < 0.

(* zwraca punkt symetryczny do (x,y) wzg. prostej ustalonej przez (x1, y1) (x2, y2) *)
let punkt_sym (x1, y1) (x2, y2) (x, y) =
    if x1 = x2 then
        (2. *. x1 -. x, y)
    else
        if y1 = y2 then
            (x, 2. *. y1 -. y)
        else
            let a1 = (y1 -. y2) /. (x1 -. x2)
            and a2 = (x2 -. x1) /. (y1 -. y2) in
            let b1 = y2 -. a1 *. x2
            and b2 = y -. a2 *. x in
            let xs = (b2 -. b1) /. (a1 -. a2) in
            let ys = a2 *. xs +. b2 in
            (2. *. xs -. x, 2. *. ys -. y)

(* [prostokat p1 p2] zwraca kartke, reprezentujaca domkniety prostokat *)
(* o bokach równoleglych do osi układu wspolrzednych i lewym dolnym rogu [p1] *)
(* a prawym górnym [p2] *)
let prostokat (x1, y1) (x2, y2) =
    function (x, y) ->
        if x >= x1 && x <= x2 && y >= y1 && y <= y2 then 1
        else 0

(* [kolko p r] zwraca kartke, reprezentujaca kółko domkniete o srodku w punkcie [p] *)
(* i promieniu [r] *)
let kolko (xs, ys) r =
    function (x, y) ->
        if (dst (x, y) (xs, ys)) <= r then 1
        else 0

(* [zloz p1 p2 k] składa kartke [k] wzdluz prostej przechodzacej przez punkty [p1] i [p2] *)
let zloz (x1, y1) (x2, y2) paper =
    function (x, y) ->
        let (xs, ys) = punkt_sym (x1, y1) (x2, y2) (x, y) in
        if (is_on_right (x, y) (x1, y1) (x2, y2)) then 0
        else
            if (xs = x && ys = y) then
                paper (x, y)
            else
                (paper (x, y)) + (paper (xs, ys))

(* wynikiej skladaj jest zlozenie kartki przez wszystkie punkty z listy *)
let skladaj lista k =
    List.fold_left (fun acc (p1, p2) -> zloz p1 p2 acc) k lista


(* Testy *)
(* 
let test a b msg = if a<>b then (print_int a; print_string "<>"; print_int b; print_string " test: "; print_endline msg);;

let p1 = prostokat (0., 0.) (10., 10.)
let k1 = kolko (5., 5.) 5.
let l1 = [((0., 0.), (10., 10.));
((5., 0.), (10., 5.));
((10., 0.), (0., 10.));
((2.5, 0.), (2.5, 10.))];;
let l2 = [((8., 0.), (10., 2.));
((6., 0.), (10., 4.));
((4., 0.), (10., 6.));
((2., 0.), (10., 8.));
((0., 0.), (10., 10.));
((0., 2.), (8., 10.));
((0., 4.), (6., 10.));
((0., 6.), (4., 10.));
((0., 8.), (2., 10.))];;

let p2 = skladaj l1 p1
let p3 = skladaj l2 p1
let k2 = skladaj l1 k1;;

test (p2 (7., 3.)) 0 "0.1: p2";;
test (p2 (5., 8.)) 0 "0.2: p2";;
test (p2 (3., 5.)) 0 "0.3: p2";;
test (p2 (5., 5.)) 0 "0.4: p2";;
test (p2 (0., 0.)) 2 "1: p2";;
test (p2 (0., 10.)) 2  "2: p2";;
test (p2 (2.5, 2.5)) 2 "3: p2";;
test (p2 (2.5, 7.5)) 2 "4: p2";;
test (p2 (2.5, 5.)) 4 "5: p2";;
test (p2 (0., 5.)) 5 "6: p2";;
test (p2 (1., 2.)) 4 "7: p2";;
test (p2 (1., 5.)) 8 "8: p2";;
test (p2 (1., 8.)) 4 "9: p2";;

test (k2 (7., 3.)) 0 "0.1: k2";;
test (k2 (5., 8.)) 0 "0.2: k2";;
test (k2 (3., 5.)) 0 "0.3: k2";;
test (k2 (5., 5.)) 0 "0.4: k2";;
test (k2 (2.5, 2.5)) 2 "1: k2";;
test (k2 (2.5, 7.5)) 2 "2: k2";;
test (k2 (2.5, 5.)) 4 "3: k2";;
test (k2 (0., 5.)) 5 "4: k2";;
test (k2 (1., 3.)) 4 "5: k2";;
test (k2 (1., 5.)) 8 "6: k2";;
test (k2 (1., 7.)) 4 "7: k2";;

test (p3 ((-4.), 6.)) 2 "1: p3";;
test (p3 ((-3.), 5.)) 1 "2: p3";;
test (p3 ((-3.), 7.)) 2 "3: p3";;
test (p3 ((-2.), 6.)) 3 "4: p3";;
test (p3 ((-2.5), 6.5)) 4 "5: p3";;
test (p3 ((-2.), 8.)) 4 "6: p3";;
test (p3 ((-1.), 7.)) 3 "7: p3";;
test (p3 ((-1.5), 7.5)) 6 "8: p3";;
test (p3 (0., 8.)) 5 "9: p3";;
test (p3 ((-1.), 9.)) 4 "10: p3";;
test (p3 ((-0.5), 8.5)) 8 "11: p3";;
test (p3 (0., 10.)) 6 "12: p3";;
test (p3 (1., 9.)) 5 "13: p3";;
test (p3 (0.5, 9.5)) 10 "14: p3";;

let kolo = kolko (0.,0.) 10. in
assert (kolo (1000., 0.) = 0);
let poziomo = zloz (0.,0.) (1.,0.) kolo in
assert (poziomo (0.,0.) = 1);
assert (poziomo (0.,1.) = 2);
assert (poziomo (0.,-1.) = 0);
let pionowo = zloz (0.,0.) (0.,1.) kolo in
assert (pionowo (0.,0.) = 1);
assert (pionowo (-1.,0.) = 2);
assert (pionowo (1.,0.) = 0);
let cwiartka = zloz (0.,0.) (0.,1.) poziomo in
assert (cwiartka (0.,0.) = 1);
assert (cwiartka (-1.,1.) = 4);
assert (cwiartka (-1.,0.) = 2); 
*)
