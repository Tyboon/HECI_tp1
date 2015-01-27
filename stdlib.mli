type bot

type ('a,'b) et
type ('a,'b) ou
type 'a neg

val bot_elim : bot -> 'a

val neg_elim : 'a -> 'a neg -> bot
val neg_intro : ('a -> bot) -> 'a neg

val and_intro : 'a -> 'b -> ('a, 'b) et
val and_elim_l : ('a, 'b) et -> 'a
val and_elim_r : ('a, 'b) et -> 'b

val or_intro_l : 'a -> ('a, 'b) ou
val or_intro_r : 'b -> ('a, 'b) ou
val or_elim : ('a -> 'c) -> ('b -> 'c) -> ('a, 'b) ou -> 'c

(*** warning : |)0 |\\|0+ |2|_||\\| +|-|!5 0|2 +|-|3 \\|/0|21|) \\|/!11 (0114|>53 ***)
val negneg_elim : 'a neg neg -> 'a
