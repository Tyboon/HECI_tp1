(** Dans ce pseudo-TP, on va utiliser un "assistant de preuve"
    rudimentaire basé sur le système de type de Caml.

    Le terme "assistant de preuve" est très mal choisi, car le système
    ne vous assiste pas. Au contraire, il vous embête jusqu'à ce que
    votre "preuve" soit CORRECTE. Dans ce sens-la, il vous assiste à
    faire des preuves correctes.

    Il y a un module qui s'appelle Stdlib, fourni avec son interface,
    qui est, elle, soit-disant lisible par des êtres humains.

    Vous devez compiler le tout avec les commandes :

    ocamlc -c stdlib.mli
    ocamlc -c stdlib.ml

    Vous pouvez enfin charger le système :
**)

#load "stdlib.cmo";;
open Stdlib;;

(** pour commencer en douceur, on va démontrer que le ET est
commutatif : écrivez une fonction de type

('a, 'b) et -> ('b, 'a) et

Vous devez pour ça utiliser les fonctions du module Stdlib.
**)

let and_commute a_et_b = 
     let a = and_elim_l a_et_b in
     let b = and_elim_r a_et_b in
     and_intro b a;;

(** même topo avec l'associativité : écrivez une fonction de type

('a, ('b, 'c) et) et -> (('a, 'b) et, 'c) et

**)

let and_associatif abc = 
        let a = and_elim_l abc in
        let bc = and_elim_r abc in
        let c = and_elim_l bc in
        let b = and_elim_r bc in
        let ab = and_intro a b in
        and_intro ab c;; 
(** Enfin, voici une sélection de petites choses "faciles" :

('a, 'b) et -> 'a
('a, 'a -> 'b) et -> 'b
('a, ('a, 'b) et) ou -> 'a
('a, 'a) ou -> 'a
('a, 'b) ou -> ('b, 'a) ou
'a -> 'a neg neg

**)

(** ('a, 'b) et -> 'a **)
let first ab = 
        let a = and_elim_r ab in
        a;;

(** ('a, 'a -> 'b) et -> 'b **)
let applic af = 
        let a = and_elim_l af in
        let f = and_elim_r af in
        let r = f a in
        r ;;

(** ('a, ('a, 'b) et) ou -> 'a **)

let or_1 a_ou_ab =
        let cas_gauche a = a in
        let cas_droite ab = and_elim_l ab in
        or_elim cas_gauche cas_droite a_ou_ab;;

(**  ('a, 'a) ou -> 'a **)

let or_2 a_ou_a = 
        let cas_gauche a = a in
        let cas_droite a = a in
        or_elim cas_gauche cas_droite a_ou_a;;

(** ('a, 'b) ou -> ('b, 'a) ou **)

let or_associatif a_ou_b = 
        let cas_gauche = or_intro_r in
        let cas_droite  = or_intro_l in
        or_elim cas_gauche cas_droite a_ou_b;;

(** 'a -> 'a neg neg **)
let easy_version a =
        let non_a_donne_contradiction non_a =
                neg_elim a non_a 
        in
        neg_intro non_a_donne_contradiction;;

let medium_version a = neg_intro (fun non_a -> neg_elim a non_a);;

let expert_version a = neg_intro (neg_elim a) ;;


(** maintenant les choses dures. Il y a deux sources de difficulté, le
"OU" qui oblige à des raisonnements par cas, et la négation qui oblige
à faire des "raisonnements par l'absurde".

('a, ('b, 'c) ou) ou -> (('a, 'b) ou, 'c) ou
('a, ('b, 'c) ou) et -> (('a, 'b) et, ('a, 'c) et) ou
(('a, 'b) et, ('a, 'c) et) ou -> ('a, ('b, 'c) ou) et
('a, ('b, 'c) et) ou -> (('a, 'b) ou, ('a, 'c) ou) et
(('a, 'b) ou, ('a, 'c) ou) et -> ('a, ('b, 'c) et) ou
('a, 'b) et -> ('a neg, 'b neg) ou neg**)

let crazy ab =
        let a = and_elim_l ab in
        let b = and_elim_r ab in
        let na_ou_nb_donne_contradiction na_ou_nb =
                let cas_gauche na = neg_elim a na in
                let cas_droite nb = neg_elim b nb in
                or_elim cas_gauche cas_droite na_ou_nb
        in
        neg_intro na_ou_nb_donne_contradiction;;


let crazier ab = 
        neg_intro (or_elim(neg_elim(and_elim_l ab))(neg_elim(and_elim_r ab)));;
(**
('a, 'b) ou -> ('a neg, 'b neg) et neg
('a, 'b) ou -> ('a neg, 'b neg) et neg
('a neg, 'b neg) et -> ('a, 'b) ou neg
('a, 'b) ou neg -> ('a neg, 'b neg) et
('a, 'b) ou -> 'a neg -> 'b
('a neg, 'b) ou -> 'a -> 'b

*)

(** Et pour finir les "horribles" : ceux où l'emploi de la fonction
    negneg_elim est indispensable (personne ne sait trop ce qui peut
    se passer si on l'exécute...

('a neg -> bot) -> 'a
unit -> ('a, 'a neg) ou
(('a -> 'b) -> 'a) -> 'a

*)
