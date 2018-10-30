(* Autor: Kamil Poniewierski *)

(*  definicja *)
(*  lewy oraz prawy koniec przedzialu, *)
(*  Przedzial oznacza normalny przedzial, Dopelnienie to R - Przedial utworzony z tej samej pary *)
type wartosc =
    | Przedzial of float * float
    | Dopelnienie of float * float
    | Pusty

(* konstruktory *)

(* wartosc_dokladnosc x p = x +/- p% *)
(* war.pocz.: p > 0                  *)
let wartosc_dokladnosc x p =
    assert (p > 0.);
    let k = abs_float (p *. x /. 100.) in (* x * p % *)
    Przedzial (x -. k, x +. k)

(* wartosc_od_do x y = [x;y]         *)
(* war.pocz.: x <= y                 *)
let wartosc_od_do x y =
    assert (x <= y);
    Przedzial (x, y)

(* wartosc_dokladna x = [x;x]        *)
let wartosc_dokladna x =
    Przedzial (x, x)

(* funkcje pomocnicze *)
let is_inf x = classify_float x = FP_infinite
let is_nan x = classify_float x = FP_nan

let safe_min a b =
    if is_nan a then b
    else if is_nan b then a
    else min a b
let min = safe_min (* nadpisanie min w celu obslugiwania nan *)

let safe_max a b =
    if is_nan a then b
    else if is_nan b then a
    else max a b
let max = safe_max;; (* analogicznie do nadpisania min *)

(* min/max z czterech liczb *)
let min_of_four a b c d = min (min a b) (min c d)
let max_of_four a b c d = max (max a b) (max c d)

(* min/max iloczyn z czterech liczb *)
let min_iloczyn a b c d = min_of_four (a *. c) (a *. d) (b *. c) (b *. d)
let max_iloczyn a b c d = max_of_four (a *. c) (a *. d) (b *. c) (b *. d)

(* in_wartosc w x = x \in w *)
let in_wartosc w x =
    match w with
    | Przedzial (a, b) -> (a <= x) && (x <= b)      (* x jest w srodku przedzialu *)
    | Dopelnienie (a, b) -> (x <= a) || (b <= x)    (* x jest po ktorejs stronie *)
    | Pusty -> false

(* oblicza przedzial przeciwny *)
let przeciwny w = 
    match w with
    | Pusty -> Pusty
    | Dopelnienie (a, b) when a = b -> Przedzial (neg_infinity, infinity)
    | Dopelnienie (a, b) -> Dopelnienie (min (0. -. a) (0. -. b), max (0. -. a) (0. -. b))
    | Przedzial (a, b) -> Przedzial (min (0. -. a) (0. -. b), max (0. -. a) (0. -. b))

(* oblicza przedzial odwrotny *)
let odwrotny w =
    match w with
    | Pusty -> Pusty 
    | Przedzial (a, b) when a = neg_infinity && b = infinity -> 
        Przedzial (neg_infinity, infinity)
    | Przedzial (0., 0.) -> Pusty
    | Przedzial (0., b) -> Przedzial (1. /. b, infinity)
    | Przedzial (a, 0.) -> Przedzial (neg_infinity, 1. /. a)
    | Przedzial (a, b) when (in_wartosc (Przedzial (a, b)) 0.) -> Dopelnienie (1. /. a, 1. /. b)
    | Przedzial (a, b) -> Przedzial (min (1. /. a) (1. /. b), max (1. /. a) (1. /. b))
    | Dopelnienie (a, b) when a = b -> Przedzial (neg_infinity, infinity)
    | Dopelnienie (a, b) when (in_wartosc (Dopelnienie (a, b)) 0.) ->
        Dopelnienie (min (1. /. a) (1. /. b), max (1. /. a) (1. /. b))
    | Dopelnienie (a, b) ->
        Przedzial (min (1. /. a) (1. /. b), max (1. /. a) (1. /. b))

(* lewa strona Dopelnienia, jeden z dwoch przedzialow *)
let split_lewy w =
    match w with
    | Dopelnienie (a, _) -> Przedzial (neg_infinity, a)
    | x -> x

(* prawa strona Dopelnienia, jeden z dwoch przedzialow *)
let split_prawy w =
    match w with
    | Dopelnienie (_, b) -> Przedzial (b, infinity)
    | x -> x



(* min_wartosc w = najmniejsza możliwa wartość w,   *)
(* lub neg_infinity jeśli brak dolnego ograniczenia.*)
(*val min_wartosc: wartosc -> float *)
let min_wartosc w =
    match w with
    | Przedzial (a, b) -> a
    | Dopelnienie (a, b) -> neg_infinity
    | Pusty -> nan

(* max_wartosc w = największa możliwa wartość w,    *)
(* lub infinity jeśli brak górnego ograniczenia.    *)
(* val max_wartosc: wartosc -> float *)
let max_wartosc w =
    match w with
    | Przedzial (a, b) -> b
    | Dopelnienie (a, b) -> infinity
    | Pusty -> nan

(* środek przedziału od min_wartosc do max_wartosc, *)
(* lub nan jeśli min i max_wartosc nie są określone.*)
(* val sr_wartosc:  wartosc -> float *)
let sr_wartosc w =
    match w with
    | Przedzial (a, b) when (is_inf) a && (is_inf b) -> nan
    | Przedzial (a, b) when (a = neg_infinity) -> neg_infinity
    | Przedzial (a, b) when (b = infinity) -> infinity
    | Przedzial (a, b) -> (a +. b) /. 2.
    | Dopelnienie (_, _) -> nan
    | Pusty -> nan

let rec sumuj x y =
    match x, y with
    | Przedzial (a, b), Przedzial (c, d) -> if (a = neg_infinity && d = infinity)
        then
            (
                if b >= c (* przedzialy maja czesc wspolna *)
                then Przedzial (neg_infinity, infinity)
                else Dopelnienie (b, c) (* przedzialy sa rozlaczne *)
            )
        else if (b = infinity && c = neg_infinity) then
            (
                if a < d (* przypadek analogiczny do tego powyzej, inna kolejnosc *)
                then Przedzial (neg_infinity, infinity)
                else Dopelnienie (d, a)
            )
        else Przedzial (min a c, max b d)
    | Przedzial (a, b), Dopelnienie(c, d) ->
        sumuj (sumuj x (split_lewy y)) (sumuj x (split_prawy y))
    | Dopelnienie (_, _), Przedzial (_, _)-> sumuj y x
    | Dopelnienie (a, b), Dopelnienie (c, d) -> Dopelnienie (max a c, min b d)
    | Pusty, _ -> Pusty
    | _, Pusty -> Pusty

let rec ogolne_dzialanie x y f =
    match (x, y) with
    | _, Pusty -> Pusty
    | Pusty, _ -> Pusty
    | Przedzial (_, _), Przedzial (_, _) -> f x y
    | Przedzial (_, _), Dopelnienie (_, _) ->
        let k = ogolne_dzialanie x (split_lewy y) f
        and l = ogolne_dzialanie x (split_prawy y) f in
            sumuj k l
    | Dopelnienie (_, _), Przedzial (_, _) -> ogolne_dzialanie y x f
    | Dopelnienie (_, _), Dopelnienie (_, _) ->
        let k = ogolne_dzialanie (split_lewy x) (split_lewy y) f
        and l = ogolne_dzialanie (split_lewy x) (split_prawy y) f
        and m = ogolne_dzialanie (split_prawy x) (split_lewy y) f
        and n = ogolne_dzialanie (split_prawy x) (split_prawy y) f in
        sumuj (sumuj k l) (sumuj m n)

(* Operacje arytmetyczne na niedokładnych wartościach. *)

let rec plus x y = 
    match (x, y) with
    | (Przedzial (a, b), Przedzial (c, d)) -> (Przedzial (a +. c, b +. d))
    | a, b -> ogolne_dzialanie a b plus

let minus x y =
    plus x (przeciwny y)

let rec razy x y =
    match x, y with
    | Przedzial (a, b), Przedzial (c, d) -> let zero = wartosc_dokladna 0. in
        if x = zero || y = zero then zero
        else
            Przedzial(min_iloczyn a b c d, max_iloczyn a b c d)
    | a, b -> ogolne_dzialanie a b razy

let podzielic x y = razy x (odwrotny y)

(*let a = wartosc_od_do (-1.) 1.            (* <-1, 1> *)
let b = wartosc_dokladna (-1.)            (* <-1, -1> *)
let c = podzielic b a                     (* (-inf -1> U <1 inf) *)
let d = plus c a                          (* (-inf, inf) *)
let e = wartosc_dokladna 0.               (* <0, 0> *)
let f = razy c e                          (* <0, 0> *)
let g = razy d e                          (* <0, 0> *)
let h = wartosc_dokladnosc (-10.) 50.     (* <-15, -5> *)
let i = podzielic h e                     (* nan, przedzial pusty*)
let j = wartosc_od_do (-6.) 5.            (* <-6, 5> *)
let k = razy j j                          (* <-30, 36> *)
let l = plus a b                          (* <-2, 0> *)
let m = razy b l                          (* <0, 2> *)
let n = podzielic l l                     (* <0, inf) *)
let o = podzielic l m                     (* (-inf, 0) *)
let p = razy o a                          (* (-inf, inf) *)
let q = plus n o                          (* (-inf, inf) *)
let r = minus n n                         (* (-inf, inf) *)
let s = wartosc_dokladnosc (-0.0001) 100. (* <-0.0002, 0> *)
let t = razy n s;;                        (* (-inf, 0) *)

assert ((min_wartosc c, max_wartosc c) = (neg_infinity, infinity));
assert (is_nan (sr_wartosc c) );
assert (not (in_wartosc c 0.));
assert ((in_wartosc c (-1.)) && (in_wartosc c (-100000.)) && (in_wartosc c 1.) && (in_wartosc c 100000.));
assert ((in_wartosc d 0.) && (in_wartosc d (-1.)) && (in_wartosc d (-100000.)) && (in_wartosc d 1.) && (in_wartosc d 100000.));
assert ((min_wartosc f, max_wartosc f, sr_wartosc f) = (0., 0., 0.));
assert ((min_wartosc g, max_wartosc g, sr_wartosc g) = (0., 0., 0.));
assert ((min_wartosc h, max_wartosc h, sr_wartosc h) = (-15., -5., -10.));
assert (is_nan (min_wartosc i) && is_nan (sr_wartosc i) && is_nan (max_wartosc i));
assert ((min_wartosc k, max_wartosc k, sr_wartosc k) = (-30., 36., 3.));
assert ((min_wartosc n, max_wartosc n, sr_wartosc n) = (0., infinity, infinity));
assert ((min_wartosc o, max_wartosc o, sr_wartosc o) = (neg_infinity, 0., neg_infinity));
assert ((min_wartosc p, max_wartosc p, is_nan (sr_wartosc p)) = (neg_infinity, infinity, true));
assert ((min_wartosc q, max_wartosc q, is_nan (sr_wartosc q)) = (neg_infinity, infinity, true));
assert ((min_wartosc r, max_wartosc r, is_nan (sr_wartosc r)) = (neg_infinity, infinity, true));
assert ((min_wartosc t, max_wartosc t, sr_wartosc t) = (neg_infinity, 0., neg_infinity));;

let a = wartosc_od_do neg_infinity infinity
let c = plus a a
let d = razy a a
let e = podzielic a a
let f = minus a a;;
assert ((min_wartosc c, max_wartosc c, is_nan (sr_wartosc c)) = (neg_infinity, infinity, true));
assert ((min_wartosc d, max_wartosc d, is_nan (sr_wartosc d)) = (neg_infinity, infinity, true));
assert ((min_wartosc e, max_wartosc e, is_nan (sr_wartosc e)) = (neg_infinity, infinity, true));
assert ((min_wartosc d, max_wartosc d, is_nan (sr_wartosc d)) = (neg_infinity, infinity, true));;

let a = wartosc_od_do 0. infinity
let b = wartosc_dokladna 0.
let c = podzielic a b
let d = podzielic b b;;
assert ((is_nan(min_wartosc c), is_nan(max_wartosc c), is_nan (sr_wartosc c)) = (true, true, true));
assert ((is_nan(min_wartosc d), is_nan(max_wartosc d), is_nan (sr_wartosc d)) = (true, true, true));;

let a = wartosc_od_do (-10.) 10.
let b = wartosc_od_do (-1.) 1000.
let c = podzielic a b;;
assert ((min_wartosc c, max_wartosc c, is_nan (sr_wartosc c)) = (neg_infinity, infinity, true));;

let a = wartosc_od_do (-1.0) 1.0
let b = wartosc_dokladna 1.0
let c = podzielic b a
let d = wartosc_dokladna 3.0
let e = plus c d      (* (-inf, 2> U <4 inf) *)
let f = podzielic b e (* (-inf, 1/4> U <1/2, inf) *)
let g = podzielic d a (* (-inf, -3> U <3, inf) *)
let h = podzielic g f (* (-inf, inf *)
let i = plus f g;;    (* (-inf, inf) *)

assert ((in_wartosc f 0.25, in_wartosc f 0.26, in_wartosc f 0.49, in_wartosc f 0.50)=(true, false, false, true));
assert ((min_wartosc h, max_wartosc h, is_nan (sr_wartosc h), in_wartosc h 0.) = (neg_infinity, infinity, true, true));
assert ((min_wartosc h, max_wartosc h, is_nan (sr_wartosc h), in_wartosc h 0.3) = (neg_infinity, infinity, true, true));;

let jed = wartosc_dokladna 1.
let zero = wartosc_dokladna 0.;;
assert ((sr_wartosc zero, max_wartosc zero, min_wartosc zero) = (0.,0.,0.));;

let a = wartosc_od_do 0. 1. (* <0,1> *)
let b = podzielic a a       (* <0, inf)*)
let c = razy b zero;;       (* <0,0> *)
assert ((sr_wartosc c, max_wartosc c, min_wartosc c) = (0.,0.,0.));;

let a = podzielic jed zero;; (* nan *)
assert (is_nan (min_wartosc a));
assert (is_nan (max_wartosc a));
assert (is_nan (sr_wartosc a));;

let a = wartosc_dokladnosc 1. 110.;; (* <-0.1, 2.1> *)
assert (in_wartosc a (-.0.1));
assert (in_wartosc a (2.1));;

let a = wartosc_od_do (-.3.) 0.  (* <-3.0, 0.0> *)
let b = wartosc_od_do 0. 1.      (* <-0.0, 1.0> *)
let c = podzielic a b;;          (* (-inf, 0> *)
assert (max_wartosc c = 0.);
assert (min_wartosc c = neg_infinity);
assert (sr_wartosc c = neg_infinity);;

let a = wartosc_od_do 1. 4.     (* <1.0, 4.0> *)
let b = wartosc_od_do (-.2.) 3. (* <-2.0, 3.0> *)
let c = podzielic a b           (* (-inf, -1/2> U <1/3, inf) *)
let d = podzielic c b           (* (-inf, -1/6> U <1/9, inf) *)
let e = plus d jed              (* (-inf, 5/6> U <10/9, inf) *)
let f = sr_wartosc (podzielic jed (wartosc_dokladna 9.));; (* 1/9 *)
assert (is_nan (sr_wartosc d));
assert (in_wartosc d 0.12);
assert (not (in_wartosc d 0.));
assert (not (in_wartosc d (-0.125)));
assert (in_wartosc d f);
assert (not (in_wartosc e 1.));;

(* uwaga, ten test moze sie zawiesic przy pewnych implementacjach! *)
let a = wartosc_od_do (-2.) 3.
let b = wartosc_od_do 2. 3.
let c = podzielic b a

let rec iteruj f n acc = match n with
    | 0 -> acc
    | n when n > 0 -> iteruj f (n-1) (f acc acc)
    | _ -> acc

let x = iteruj razy 10 c;;
assert (not (in_wartosc x 0.));;
*)