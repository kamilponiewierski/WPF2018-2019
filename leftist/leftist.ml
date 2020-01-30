(*  Autor: Kamil Poniewierski
    Recenzent: Łukasz Wcisło *)

(** Typ złączalnej kolejki priorytetowej *)
type 'a queue =
    | Null
    | Node of 'a queue * 'a * 'a queue * int

(* wyjatek dla pustej kolejki *)
exception Empty

(* konstruktory *)
let empty = Null

let pojedynczy x = Node (Null, x, Null, 1)

(* funkcje pomocnicze *)
let get_left q =
    match q with
    | Null -> raise Empty
    | Node (left, _, _, _) -> left

let get_right q =
    match q with
    | Null -> raise Empty
    | Node (_, _, right, _) -> right

let priority q =
    match q with
    | Null -> raise Empty
    | Node (_, priority, _, _) -> priority

let height q =
    match q with
    | Null -> -1
    | Node (_, _, _, height) -> height

(* sprawdza czy kolejka jest pusta *)
let is_empty q = q = Null

(* laczy kolejki q1 i q2 *)
let rec join q1 q2 =
    match q1, q2 with
    | (Null, q2) -> q2
    | (q1, Null) -> q1
    | (q1, q2) ->
        if priority q2 < priority q1
            then join q2 q1
        else
            let temp_c = join (get_right q1) q2 in
            let h_q1_left = height (get_left q1) and h_c = height temp_c in
            if h_c <= h_q1_left then
                Node (get_left q1, priority q1, temp_c, h_c + 1)
            else
                Node (temp_c, priority q1, get_left q1, h_q1_left + 1)

(* usuwa z kolejki najmniejszy element i zwraca drzewo bez niego *)
let delete_min q =
    match q with
    | Null -> raise Empty
    | _ -> (priority q, join (get_left q) (get_right q))

(* dodaje do drzewa q element x *)
let add x q =
    join q (pojedynczy x)
