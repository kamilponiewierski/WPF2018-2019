(*
 * ISet - Interval sets
 * Copyright (C) 1996-2003 Xavier Leroy, Nicolas Cannasse, Markus Mottl, Jacek Chrzaszcz
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version,
 * with the special exception on linking described in file LICENSE.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

(** Interval Set.

    This is an interval set, i.e. a set of integers, where large
    intervals can be stored as single elements. Intervals stored in the
    set are disjoint. 

*)

type interval = {left: int; right: int}

type tree =
    | Empty
    | Node of tree * interval * tree * int * int  

type t = tree

(* konstruktor pustego tree *)
let empty = Empty

(* sprawdza czy tree jest puste *)
let is_empty t = t = Empty

(* zwraca wysokosc Node *)
let height t =
    match t with
    | Empty -> 0
    | Node (_, _, _, height, _) -> height

(* zwraca rozmiar Node *)
let size t =
    match t with
    | Empty -> 0
    | Node (_, _, _, _, size) -> size

(* tworzy przedzial *)
let interval left right =
    assert (left <= right);
    {left = left; right = right}

(* oblicza rozmiar interwalu, zabezpieczone przed overflow *)
let i_size i =
    if i.right - i.left + 1 <= 0 then 
        max_int
    else i.right - i.left + 1

(* bezpieczne dodawanie, zabezpieczone przed overflow *)
let safe_add a b =
    if max_int - a < b then max_int else a + b

(* oblicza rozmiar drzewa, tj sumuje rozmiary poddrzew i interwalu w danym Node *)
let safe_size l i r = safe_add (safe_add (size l) (size r)) (i_size i)

(* poprzednik liczby x, zabezpieczony przed underflow *)
let pred x = if x = min_int then min_int else x - 1

(* nastepnik liczby x, zabezpieczony przed overflow *)
let succ x = if x =  max_int then max_int else x + 1

(* funkcja porownujaca dwa interwaly *)
let compare_interval i j =
    (* i jest mniejsze od j, czyli max i jest mniejszy od min j*)
    if (succ i.left) < j.left && (succ i.right) < j.left then -1
    (* j jest mniejsze od i, analogicznie *)
    else if succ j.left < i.left && succ j.right < i.left then 1
    (* zbiory mozna polaczyc *)
    else 0

(* tworzy node o poddrzewach l, r i interwale k *)
let make l k r =
    let size = safe_size l k r in
    Node (l, k, r, max (height l) (height r) + 1, size)

(* balansuje drzewo, zmienia wysokosc maksymalnie o 1 *)
let bal l k r =
    let hl = height l in
    let hr = height r in
    if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _, _) ->
        if height ll >= height lr then make ll lk (make lr k r)
        else
          (match lr with
          | Node (lrl, lrk, lrr, _, _) ->
              make (make ll lk lrl) lrk (make lrr k r)
          | Empty -> assert false)
    | Empty -> assert false
    else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _, _) ->
        if height rr >= height rl then make (make l k rl) rk rr
        else
          (match rl with
          | Node (rll, rlk, rlr, _, _) ->
              make (make l k rll) rlk (make rlr rk rr)
          | Empty -> assert false)
    | Empty -> assert false
    else make l k r

type 'a flag = No | Yes of 'a

(* dodaje rozlaczny przedzial do drzewa *)
let rec add_one i = function
    | Node (l, k, r, h, _) ->
        let c = compare_interval i k in
        if c = 0 then 
            failwith "Nie jest rozlaczny"
        else 
            if c < 0 then
                let nl = add_one i l in
                bal nl k r
            else
                let nr = add_one i r in
                bal l k nr
    | Empty -> Node (Empty, i, Empty, 1, i_size i)

(* laczy dwa drzewa i balansuje je *)
let rec join l k r =
    match (l, r) with
    | (Empty, _) -> add_one k r
    | (_, Empty) -> add_one k l
    | Node(ll, lk, lr, lh, _), (Node(rl, rk, rr, rh, _)) ->
        if lh > rh + 2 then bal ll lk (join lr k r) else
        if rh > lh + 2 then bal (join l k rl) rk rr else
        make l k r 

let rec min_elt = function
    | Node (Empty, k, _, _, _) -> k
    | Node (l, _, _, _, _) -> min_elt l
    | Empty -> raise Not_found

(* usuwa najmniejszy element, po tym balansuje drzewo *)
let rec remove_min_elt = function
    | Node (Empty, _, r, _, _) -> r
    | Node (l, k, r, _, _) -> bal (remove_min_elt l) k r
    | Empty -> invalid_arg "iSet.remove_min_elt"

(* laczy ze soba dwa drzewa, korzeniem jest najmniejszy el wiekszego drzewa *)
let merge t1 t2 =
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
      let k = min_elt t2 in
      bal t1 k (remove_min_elt t2)

(* komparator, sprawdza czy liczba nalezy do interwalu *)
let interval_member x i =
    if x < i.left then -1
    else if x > i.right then 1
    else 0

(* funkcja laczaca dwa sasiednie interwaly *)
let merge_intervals i f =
    match f with
    | No -> i
    | Yes (j) ->  
        assert (abs(i.left - j.right) < 2 || abs(i.right - j.left) < 2);
        interval (min i.left j.left) (max i.right j.right)

(* drzewo przedzialow mniejszych od x, przedzial do ktorego nalezy *)
let rec split_left x t =
    match t with
    | Empty -> (Empty, No)
    | Node (l, k, r, _, _) ->
        let c = interval_member x k in
        if c = 0 then (l, Yes(interval k.left x))
        else if c < 0 then split_left x l
        else let (rl, i) = split_left x r in (join l k rl, i)

(* analogiczne do split_left, zwraca drzewo wiekszych od x i przedzial *)
let rec split_right x t =
    match t with
    | Empty -> (Empty, No)
    | Node (l, k, r, _, _) ->
        let c = interval_member x k in
        if c = 0 then (r, Yes(interval x k.right))
    else if c < 0 then let (lr, i) = split_right x l in (join lr k r, i)
    else split_right x r

(* moze dolaczyc do drzewa l przedzial zawarty w f *)
let join_left_f l f =
    match f with
    | No -> l
    | Yes (i) -> join l i empty

(* moze dolaczy do drzewa r przedzial zawarty w f *)
let join_right_f r f =
    match f with
    | No -> r
    | Yes (i) -> join empty i r

(* dodaje przedzial i do drzewa t, funkcje split tworza poddrzewa drzewa wynikowego *)
let add_interval i t =
    match t with
    | Empty -> make empty i empty
    | Node (_, _, _, _ , _) -> 
        let (lt, li) = split_left (pred i.left) t
        and (rt, ri) = split_right (succ i.right) t
        in let pom = merge_intervals i li
        in let merged = merge_intervals pom ri
        in join lt merged rt

let add (left, right) t =
    let i = interval left right in
    add_interval i t

let remove (left, right) t =
    let i = interval left right in
    match t with
    | Empty -> Empty
    | Node (_, _, _, _, _) as t ->
        let (lt, li) = if (i.left = min_int) then (empty, No)
            else split_left (pred i.left) t
        and (rt, ri) = if (i.right = max_int) then (empty, No)
            else split_right (succ i.right) t
        in let l = join_left_f lt li
        and r = join_right_f rt ri
        in merge l r

let rec mem x t =
    match t with
    | Empty -> false
    | Node (l, k, r, _, _) -> 
        let c = interval_member x k in
        if c = 0
            then true
        else
            if c = -1 then mem x l
            else mem x r

let iter f t =
    let rec loop = function
        | Empty -> ()
        | Node (l, k, r, _, _) -> loop l; f (k.left, k.right); loop r in
    loop t

let fold f t acc =
    let rec pom acc t =
    match t with
    | Empty -> acc
    | Node (l, k, r, _, _) -> 
        pom (f (k.left, k.right) (pom acc l)) r in
    pom acc t

let elements t =
    let rec pom acc t =
        match t with
        | Empty -> acc
        | Node (l, k, r, _, _) -> pom ((k.left, k.right) :: pom acc r) l
    in pom [] t

let below x t =
    let (left_t, left_i) = split_left x t in
        join_left_f left_t left_i |> size

let rec split x t = 
    let smaller = let (lt, li) = split_left (pred x) t in
        join_left_f lt li
    and greater = let (rt, ri) = split_right (succ x) t in
        join_right_f rt ri
    and member = mem x t
    in (smaller, member, greater)