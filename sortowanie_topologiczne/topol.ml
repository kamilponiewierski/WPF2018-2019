(* Autor: Kamil Poniewierski *)
(* Review: Eliasz Wielichowski *)
open PMap;;

(* wyjatek dla cyklicznego grafu *)
exception Cykliczne

(* lista par postaci element list, el *)
let rob_pary list el =
  let rec pom list acc =
    match list with
    | [] -> acc
    | hd::tl -> pom tl ( (hd, el) :: acc )
  in pom (List.rev list) [];;

(* dodaje do "graf" strzalki wchodzace do grafu, do kolory dostawia flage 0 *)
let rob_graf (graf, kolory) (el, rel) =
  let graf = PMap.add el rel graf in
  let kolory = PMap.add el 0 kolory in
  (graf, kolory)

(* 0 - wierzcholek nieodwiedzony *)
(* 1 - wierzcholek odwiedzony, ktory nie zostal wrzucony na stos *)
(* 2 - wierzcholek na stosie *)
let rec dfs ((graf, kolory), wyn) stos =
  match stos with
  | [] -> ((graf, kolory), wyn)
  | (el, enc)::tl ->
    if not (PMap.mem el kolory) then 
    (* elementu nie bylo w kolory, zostaje dodany z flaga 2 *)
      let kolory = PMap.add el 2 kolory in
      dfs ((graf, kolory), el::wyn) tl
    else
    (* element byl w kolory, sprawdzenie czy nie trafiono na cykl *)
      let kol = PMap.find el kolory in
      if enc = 0 && kol = 1 then raise Cykliczne
      else
        if kol = 1 then
          let kolory = PMap.add el 2 kolory in 
          dfs ((graf,kolory), el::wyn) tl 
        else
          if kol = 2 then dfs ((graf, kolory), wyn) tl
          else
            let kolory = PMap.add el 1 kolory in 
            let sasiedzi = (PMap.find el graf) in
            let sasiedzi = rob_pary sasiedzi 0 in
            let stos = sasiedzi @ ((el,1) :: tl) in
            dfs ((graf, kolory), wyn) stos;;

(* sortowanie topologiczne grafu *)
let topol l =
  match l with
  | [] -> []
  | l ->
    let graf = PMap.empty and kolory = PMap.empty in
    let (graf, kolory) = List.fold_left rob_graf (graf, kolory) l in
    let pom klucz _ acc =
      dfs acc ((klucz,1)::[])
    in
    let acc = ((graf, kolory), []) in
    let ((graf, kolory), wyn) = PMap.foldi pom graf acc in
  wyn