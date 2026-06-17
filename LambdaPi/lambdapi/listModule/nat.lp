require open Stdlib.Prop;
require open Stdlib.Set;
require open Stdlib.Eq;

constant symbol N : Set;
constant symbol zero : τ N;
constant symbol succ : τ N → τ N;

symbol + : τ N → τ N → τ N;
notation + infix left 6;

rule zero + $y ↪ $y;
rule succ $x + $y ↪ succ ($x + $y);
rule $x + zero ↪ $x;