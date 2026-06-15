require open Stdlib.Prop;
require open Stdlib.Set;
require open Stdlib.Eq;
require open listModule.nat;

//A dependently typed list definition called
//ilist, used to have compile time safety.
(A : Set) inductive ilist : TYPE ≔
| Nil : ilist A
| Cons : τ A → ilist A → ilist A;

// A length-indexed list vec
constant symbol vec : Set → τ N → TYPE;
constant symbol VNil [A : Set] : vec A zero;
constant symbol VCons [A : Set] [n : τ N] : τ A → vec A n → vec A (succ n);

//The induction principal for the vec type we defined
symbol ind_vec : Π A : Set, Π p : (Π n : τ N, vec A n → Prop),
               π (p zero VNil) →
               (Π h : τ A, Π n : τ N, Π v : vec A n, π (p n v) → π (p (succ n) (VCons h v))) →
               Π n : τ N, Π v : vec A n, π (p n v);


//The function app takes two lists,
//returns the appended list
symbol app [A : Set] [n : τ N] [m : τ N] : vec A n → vec A m → vec A (n + m);

rule app VNil $l ↪ $l;
rule app (VCons $h $tl) $l ↪ VCons $h (app $tl $l);

//The function isnoc takes an element & a list,
//returns the list with the element added to its tail.
symbol isnoc [A : Set] [n : τ N] : τ A → vec A n → vec A (succ n);

rule isnoc $e (VNil) ↪ VCons $e VNil;
rule isnoc $e (VCons $h $tl) ↪ VCons $h (isnoc $e $tl);

//The function rev takes a list & returns the reversed list.
symbol rev [A : Set] [n : τ N] : vec A n → vec A n;

rule rev VNil ↪ VNil;
rule rev (VCons $h $tl) ↪ isnoc $h (rev $tl);

//The function that returns the first element of a list
symbol hd [A : Set] [n : τ N] : vec A (succ n) → τ A;

rule hd (VCons $h _) ↪ $h;

//The function that returns the tail of a list
symbol tl [A : Set] [n : τ N]  : vec A (succ n) → vec A n;

rule tl (VCons _ $tl) ↪ $tl;

