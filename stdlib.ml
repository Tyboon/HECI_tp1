type bot = | Bot

type ('a,'b) et = And of ('a * 'b);;
type ('a,'b) ou = | Or_left of ('a) | Or_right of ('b);;
type ('a) neg = ('a -> bot);;

let rec bot_elim (Bot) = bot_elim (Bot)

let neg_elim (x : 'a ) (nx : 'a neg) : bot = nx x

let neg_intro (x : 'a  -> bot ) : 'a neg  =  x

let and_intro ( x) ( y) =  (And (x,y))
let and_elim_l ( (And (x,y))) =  x
let and_elim_r ( (And (x,y))) =  y

let or_intro_l ( x) =  (Or_left x)
let or_intro_r ( x) =  (Or_right x)
let or_elim f g  ( x) =
  match
    match x with
      | Or_left x -> f ( x)
      | Or_right y -> g ( y)
  with  p ->  p;;


(*** ATTENTION, CECI PERMET LE RAISONNEMENT CLASSIQUE ***)
let rec negneg_elim (x : 'a neg neg ) : 'a  = negneg_elim x
