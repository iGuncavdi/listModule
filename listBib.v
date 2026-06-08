Module IList.
Require Import Arith.
From Equations Require Import Equations.
Import EqNotations.
Require Import Lia.
Require Import Program.Equality.
Require Import Bool.
Require Import List.
Import ListNotations.

Inductive ilist : nat -> Type :=
| Nil : ilist 0
| Cons : forall (n: nat), nat -> ilist n -> ilist (S n).

Inductive perm : list nat -> list nat -> Prop :=
| perm_nil : perm nil nil
| perm_skip : forall x l1 l2, perm l1 l2 -> perm (x :: l1) (x :: l2)
| perm_swap : forall x y l, perm (x :: y :: l) (y :: x :: l)
| perm_trans : forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.
Arguments Cons {n} _ _.

Definition length (n : nat) (ls : ilist n) : nat := n.

Equations hd (n : nat) (ls : ilist (S n)) : nat :=
hd _ (Cons h _) := h.


Eval compute in (hd 1 (Cons 1 (Cons 2 Nil))).


Equations tl (n : nat) (ls : ilist (S n)) : ilist n :=
tl _ (Cons _ t) := t.

Equations n_th (n i : nat) (ls :ilist n) : option nat :=
n_th _ _ Nil := None;
n_th _ 0 (Cons h tl) := Some h;
n_th _ (S i) (Cons h tl) := n_th _ i tl.

Equations map (n : nat) (f: nat -> nat) (ls : ilist n) : ilist n :=
map _ _ Nil := Nil;
map _ f (Cons h tl) := Cons (f h) (map _ f tl).

Equations isnoc (n : nat) (ls : ilist n) (e : nat) : ilist (S n) :=
isnoc _ Nil e := Cons e Nil;
isnoc _ (Cons h tl) e := Cons h (isnoc _ tl e).

Equations rev (n : nat) (ls : ilist n) : ilist n :=
rev _ Nil := Nil;
rev _ (Cons h tl) := isnoc _ (rev _ tl ) h.

Equations app (n1: nat) (l1 : ilist n1) (n2: nat) (l2 : ilist n2) : ilist (n1+n2) :=
app _ Nil _ l2 := l2;
app _ (Cons h1 tl1) _ ls2 := Cons h1 (app _ tl1 _ ls2).

Equations filter (n: nat) (f: nat -> bool) (l : ilist n) : list nat :=
filter _ _ Nil := nil ;
filter _ f (Cons h tl) with f h := { 
|true => cons h (filter _ f tl)
|false => filter _ f tl
}.

Equations fold_right {B : Type} (n: nat) (f: nat -> B -> B) (b: B) (l: ilist n) : B :=
fold_right _ _ a Nil := a;
fold_right _ f a (Cons h tl) := f h (fold_right _ f a tl). 

Equations fold_left {B : Type} (n: nat) (f: B -> nat -> B) (b: B) (l :ilist n) : B :=
fold_left _ _ a Nil := a;
fold_left _ f a (Cons h tl) := fold_left _ f (f a h) tl.

Equations _exists (n: nat) (f: nat -> bool) (l: ilist n) : bool :=
_exists _ _ Nil := false;
_exists _ f (Cons h tl) := (f h) || (_exists _ f tl).

Equations for_all (n: nat) (f: nat-> bool) (l: ilist n) : bool :=
for_all _ _ Nil := true;
for_all _ f (Cons h tl) := (f h) && (for_all _ f tl).

Equations find (n: nat) (f: nat -> bool) (l: ilist n) : option nat :=
find _ _ Nil := None;
find _ f (Cons h tl) with f h := {
| true => Some h
| false => find _ f tl}.

Equations insert (n: nat) (e: nat) (l: ilist n) : ilist (S n) :=
insert _ e Nil := Cons e Nil;
insert _ e (Cons h tl) with Nat.leb e h :={
| true => Cons e (Cons h tl)
| false => Cons h (insert _ e tl)
}.

Equations sort (n : nat) (l : ilist n) : ilist n :=
sort _ Nil := Nil;
sort _ (Cons h tl) := insert _ h (sort _ tl).

Equations length' (l : list nat) : nat :=
length' nil := 0;
length' (cons _ tl) := S (length' tl).

Equations inject (l : list nat) : ilist (length' l) :=
inject nil := Nil;
inject (cons x tl) := Cons x (inject tl).

Equations unject (n : nat) (l : ilist n) : list nat :=
unject _ Nil := nil;
unject _ (Cons h t) := cons h (unject _ t).

Inductive ilist2 (n : nat) : nat -> Type :=
| Nil2 : ilist2 n 0
| Cons2 : forall (k : nat), ilist n -> ilist2 n k -> ilist2 n (S k).

(*Flatten will only work if the sublist have the same length*)
Equations flatten (n k : nat) (l: ilist2 n k) : ilist (k * n) :=
flatten _ _ Nil2 := Nil;
flatten n k (Cons2 k h tl) := app n h (k * n) (flatten n k tl).

Equations combine (n : nat) (l1: ilist n) (l2: ilist n) : list (nat * nat):=
combine _ Nil Nil := nil;
combine n0 (Cons h1 tl1) (Cons h2 tl2) := cons (h1, h2) (combine _ tl1 tl2).

(* Some Lemmas*)

Lemma app_nil : forall (n : nat) (l : ilist n), 
  unject _ (app n l 0 Nil) = unject _ l.
Proof.
intros n l.
funelim (app n l 0 Nil).
simp unject.
reflexivity.

simp app.
simpl.
simp unject.

rewrite H.
reflexivity.
Qed.
(*
induction l.
simp app.
simpl.
reflexivity.
simp app.
simp unject.
rewrite <- IHl.
reflexivity.

Modelisation des vecteurs en coq
*)

Lemma app_nil2 : forall (n : nat) (l : ilist n),
  rew [ilist] (Nat.add_0_r n) in (app n l 0 Nil) = l.
Proof.
induction l.


simpl_eq.
reflexivity.
simp app.
rewrite <- IHl.
simpl_eq.

(*
rewrite app_nil.
rewrite(Nat.add_0_r n).
simp app.
*)


Admitted.
Require Import Coq.Logic.JMeq.
(*
John Major Equality

*)
Lemma app_nil3 : forall (n : nat) (l : ilist n),
  JMeq (app n l 0 Nil) l.
Proof.
intros.
funelim (app n l 0 Nil).
simp app.
reflexivity.
simp app.

Admitted.
(*
Eq_dep.dec :
Proving that there is only one proof of x = x
i.e. refl_equal x. This is true only when the equality
upon the set of x is decidable.
Its lemma :
UIP_dec : forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y})
          (x : A) (p q : x = x), p = q 
*)
Inductive heq {A : Type} (x : A) : forall {B : Type}, B -> Prop :=
| heq_refl : heq x x.

Notation "x ~= y" := (heq x y) (at level 70).
Lemma app_nil4 : forall (n : nat) (l : ilist n),
  app n l 0 Nil ~= l.
Proof.
intros.
funelim (app n l 0 Nil).
simp app.
reflexivity.
simp app.

inversion H.
simpl in H1.
Admitted.
Check unject.
Lemma app_assoc : forall (n1 n2 n3 : nat) (l1 : ilist n1) (l2 : ilist n2) (l3 : ilist n3),
  unject _ (app _ (app _ l1 _ l2) _ l3) = unject _ (app _ l1 _ (app _ l2 _ l3)).
Proof.
intros.
funelim  (app n1 l1 n2 l2).
simp app.
simpl.
reflexivity.
simp app.
simpl.
simp unject.
simp app.
rewrite <- H.
reflexivity.
Qed.


Lemma app_com_cons : forall (n1 n2 : nat) (l1 : ilist n1) (l2 : ilist n2) (h : nat),
  unject _ (app _ (Cons h l1) _ l2) = unject _ (Cons h (app _ l1 _ l2)).
Proof.
intros.
funelim (app n1 l1 n2 l2).
simp app.
simp unject.
reflexivity.
simp app.
simp unject.
rewrite <- H.
simpl.
reflexivity.
Qed.
Lemma app_nil_unject : forall (n1 n2 : nat) (l1 : ilist n1) (l2 : ilist n2),
  unject _ (app _ l1 _ l2) = nil ->
  unject _ l1 = nil /\ unject _ l2 = nil.
Proof.
  intros n1 n2 l1 l2 H.
  induction l1.
  - simp app in H. simp unject. split. reflexivity. exact H.
  - simp app in H. simp unject in H. discriminate H.
Qed.

Lemma app_eq_unit : forall (n1 n2: nat) (l1 : ilist n1) (l2 : ilist n2) (h : nat),
unject _ (app _ l1 _ l2) = unject _ (Cons h Nil) -> (unject _ l1 = nil /\ unject _ l2 = cons h nil \/ unject _ l1 = cons h nil /\ unject _ l2 = nil).
Proof.
intros n1 n2 l1 l2 h H.
induction l1.
simp app in H.
simp unject in H.
simp unject.
left.
split.
reflexivity.

apply H.
simp app in H.
simp unject in H.
simpl in H.
simp unject.

(* The fix stuff we see are the underlying 
definitions of unject and app. That's how equations define them.
So when inversion substitues them, it needs check that each
substitued type is correct
inversion H.
Here that is (S (n + n2)) *)
simp unject in H.

injection H.
intros Htl Hh.
subst.
right. split.
apply app_nil_unject in Htl.
destruct Htl as [Hl1 _].
rewrite Hl1.
reflexivity.
apply app_nil_unject in Htl.
destruct Htl as [_ Hl2].
exact Hl2.
Qed.
Lemma map_id : forall (n : nat) (l : ilist n),
  unject _ (map n (fun x => x) l) = unject _ l.
Proof.
intros.
funelim (map n (fun x : nat => x) l).
simp unject.
simp map.
simp unject.
reflexivity.
simp map.
simp unject.
rewrite <- H.
reflexivity.
Qed.

Lemma map_compose : forall (n : nat) (f g : nat -> nat) (l : ilist n),
  unject _ (map n (fun x => f (g x)) l) = unject _ (map n f (map n g l)).
Proof.
intros.
funelim (map n (fun x : nat => f (g x)) l).
simp map.
reflexivity.
simp map.
simp unject.
rewrite <- H.
reflexivity.
Qed.



Lemma unject_app : forall (n1 n2 : nat) (l1 : ilist n1) (l2 : ilist n2),
  unject _ (app _ l1 _ l2) = (unject _ l1 ++ unject _ l2).
Proof.
intros.
funelim (app n1 l1 n2 l2).
simpl.
simp unject.
simpl.
simp app.
reflexivity.
simp app.
simp unject.
simpl.
rewrite <- H.
simp unject.
reflexivity.
Qed.
Lemma isnoc_unject : forall (n : nat) (l : ilist n) (e : nat),
  unject _ (isnoc n l e) = (unject _ l ++ (e :: nil)).
Proof.
intros.
funelim (isnoc n l e).
simp isnoc.
simp unject.
simpl.
reflexivity.
simp isnoc.
simp unject.
rewrite H.
reflexivity.
Qed.
Check map.
Check unject.
Check List.map.
Lemma map_unject : forall (n : nat) (f: nat -> nat) (l : ilist n),
unject _ (map n f l) = List.map f (unject _ l).
Proof.
intros.
funelim (map n f l).
simp map.
simp unject.
reflexivity.
simp map.
simp unject.
simpl.
rewrite H.
reflexivity.
Qed.
Lemma unject_length : forall (n : nat) (l : ilist n),
  length' (unject n l) = n.
Proof.
intros.
funelim (unject n l).
reflexivity.
simp unject.
simpl.
rewrite length'_equation_2.
rewrite H.
reflexivity.
Qed.
Lemma insert_unject : forall (n : nat) (e : nat) (l : ilist n),
  length' (unject _ (insert n e l)) = S n.
Proof.
intros.
induction l.
simp insert.
simp unject.
simpl.
reflexivity.

simp insert.
destruct (Nat.leb e n0) eqn:Heq.

simpl.
simp unject.
rewrite length'_equation_2.

simp length'.
rewrite unject_length.
reflexivity.
simpl.
simp unject.
simp length'.
rewrite unject_length.
reflexivity.
Qed.

Lemma rev_isnoc : forall (n : nat) (l : ilist n) (e : nat),
  unject _ (rev _ (isnoc n l e)) = 
  (e :: unject _ (rev n l)).
Proof.
intros.
funelim (isnoc n l e).
simp isnoc.
simp rev.
simp unject.
simp isnoc.
simp unject.
reflexivity.
simp isnoc.
simp rev.
rewrite isnoc_unject.
rewrite H.
rewrite isnoc_unject.
reflexivity.
Qed.



Lemma rev_rev : forall (n: nat) (l : ilist n), unject _ (rev n (rev n l)) = unject _ l.
Proof.
intros.
funelim (rev n l).
simp rev.

reflexivity.
simp unject.

simp rev.
rewrite rev_isnoc.
rewrite H.
reflexivity.
Qed.

Check rev_equation_2.
Lemma rev_app : forall (n1 n2 : nat) (l1 : ilist n1) (l2 : ilist n2),
  unject _ (rev _ (app _ l1 _ l2)) = 
  unject _ (app _ (rev _ l2) _ (rev _ l1)).
Proof.
intros.
funelim (app n1 l1 n2 l2).
simp app.
simp rev.
simpl.
simp unject.
rewrite app_nil.
reflexivity.
simp app.
simp rev.
simp unject.
simpl.
rewrite rev_equation_2.
rewrite isnoc_unject.
rewrite H.
rewrite unject_app.
rewrite unject_app.
rewrite isnoc_unject.
rewrite List.app_assoc.

reflexivity.
Qed.
Lemma map_app : forall (n1 n2 : nat) (f : nat -> nat) (l1 : ilist n1) (l2 : ilist n2),
  unject _ (map _ f (app _ l1 _ l2)) =
  unject _ (app _ (map _ f l1) _ (map _ f l2)).
Proof.
intros.
funelim (app n1 l1 n2 l2).
simpl.
simp app.
reflexivity.
simpl.
simp map.
simp app.
simp unject.

simp unject.
simp map.

simp unject.
rewrite (H f).
reflexivity.
Qed.

Lemma map_rev : forall (n : nat) (f : nat -> nat) (l : ilist n),
  unject _ (map n f (rev n l)) = 
  unject _ (rev n (map n f l)).
Proof.
intros.
funelim (map n f l).
simp rev.
simp map.
simp rev.
reflexivity.
rewrite map_unject.
simp map.

simp rev.
simp map.
rewrite isnoc_unject.
rewrite isnoc_unject.
rewrite List.map_app.
rewrite <- H.
simpl.
rewrite map_unject.
reflexivity.
Qed.
Print filter.
Check filter_clause_2.
Lemma find_filter : forall (n : nat) (f : nat -> bool) (l : ilist n),
  find n f l = List.hd_error (filter n f l).
Proof.
intros.
funelim (find n f l).
reflexivity.

rewrite <- Heqcall.
simp filter.
rewrite Heq.
simpl.
reflexivity.
rewrite <- Heqcall.
simp filter.
rewrite Heq.
simpl.
rewrite H.
reflexivity.
Qed.

Lemma filter_length : forall (n : nat) (f : nat -> bool) (l : ilist n),
  length' (filter n f l) <= n.
Proof.
intros.
funelim (filter n f l).
reflexivity.
rewrite <- Heqcall.
simp length'.

lia.
rewrite <- Heqcall.
lia.
Qed.

Lemma sort_length : forall (n : nat) (l : ilist n),
  length' (unject _ (sort n l)) = n.
Proof.
intros.
funelim (sort n l).
simp sort.
simp unject.
reflexivity.
simp sort.
rewrite unject_length.
reflexivity.
Qed.


Print _exists.
Print negb.
Print negb_andb.

Print eq_rect.
Lemma exists_filter : forall (n : nat) (f : nat -> bool) (l : ilist n),
  _exists n f l = negb (for_all n (fun x => negb (f x)) l).
Proof.
intros.
funelim (_exists n f l).
simp for_all.
simp _exists.
simpl.
reflexivity.
simp for_all.
simp _exists.
rewrite H.
rewrite negb_andb.
rewrite negb_involutive.
reflexivity.
Qed.

Lemma for_all_filter : forall (n : nat) (f : nat -> bool) (l : ilist n),
  for_all n f l = true <-> filter n f l = unject _ l.
Proof.
intros.
funelim (for_all n f l).
split.
simp filter.
simp unject.
simp for_all.
reflexivity.
simp filter.
simp unject.
simp for_all.
reflexivity.
simp for_all.
simp filter.
simp unject.
rewrite andb_true_iff.

split.
intro.
destruct H0 as [H1 H2].
rewrite H1.
simpl.

destruct H as [H3 H4].

apply H3 in H2.
rewrite H2.
reflexivity.
destruct H as [H3 H4].
simp filter.
intro.
simp filter.
split.
destruct (f h) eqn:Heq.
reflexivity.
simp filter in H.
assert (Hlen : length' (filter n0 f tl0) <= n0) by apply filter_length.
rewrite H in Hlen.

simp length' in Hlen.
rewrite unject_length in Hlen.
lia.
destruct (f h) eqn:Heq.
simpl in H.
injection H.
intro Htl.
apply H4.
apply Htl.
simpl in H.
assert (Hlen : length' (filter n0 f tl0) <= n0) by apply filter_length.
rewrite H in Hlen.
rewrite length'_equation_2 in Hlen.

rewrite unject_length in Hlen.
lia.
Qed.
Check List.filter.
Lemma filter_filter : forall (n : nat) (f : nat -> bool) (l : ilist n),
  List.filter f (filter n f l) = filter n f l.
Proof.
intros.
funelim (filter n f l).
reflexivity.
simp filter.
rewrite Heq.
simpl.
rewrite H.
rewrite Heq.
reflexivity.
simp filter.
rewrite Heq.
simpl.
rewrite H.
reflexivity.
Qed.

Lemma filter_app : forall (n1 n2 : nat) (f : nat -> bool) (l1 : ilist n1) (l2 : ilist n2),
filter _ f (app _ l1 _ l2) = (filter _ f l1 ++ filter _ f l2).
Proof.
intros.
induction l1.
simpl.
simp filter.
simpl.
simp app.
reflexivity.

simp app.

destruct (f n0) eqn:Heq.
simp filter.
rewrite Heq.
simpl.
rewrite <- IHl1.

simp filter.
rewrite Heq.
simpl.
reflexivity.

simp filter.
rewrite Heq.
simpl.
rewrite <- IHl1.

simp filter.
rewrite Heq.
simpl.
reflexivity.
Qed.
Print app.
Print fold_left.

Check fold_left_equation_2.

Lemma fold_left_app : forall {B : Type} (n1 n2 : nat) (f : B -> nat -> B) (b : B) (l1 : ilist n1) (l2 : ilist n2),
  fold_left _ f b (app _ l1 _ l2) = 
  fold_left _ f (fold_left _ f b l1) l2.
Proof.
  intros B n1 n2 f b l1.
  revert b.
  induction l1.
  intros b l2.
  simp app.
  simp fold_left.
  reflexivity.
  intros b l2.
  simp app.
  simp fold_left.
  simpl.
  rewrite fold_left_equation_2.
  apply IHl1.

Qed.
Check fold_right_equation_2.
Lemma fold_right_app : forall {B : Type} (n1 n2 : nat) (f : nat -> B -> B) (b : B) (l1 : ilist n1) (l2 : ilist n2),
  fold_right _ f b (app _ l1 _ l2) = 
  fold_right _ f (fold_right _ f b l2) l1.
Proof.
intros B n1 n2 f b l1.
revert b.
induction l1.
intros b l2.
simp app.
simp fold_right.
simpl.
reflexivity.
intros b l2.
simpl.
simp app.
simp fold_right.
rewrite <- fold_right_equation_2.
rewrite <- IHl1.
simp fold_right.
reflexivity.
Qed.
Lemma perm_refl : forall (l : list nat), perm l l.
Proof.
  induction l.
  apply perm_nil.
  apply perm_skip. exact IHl.
Qed.

Lemma insert_permutation : forall (n : nat) (e : nat) (l : ilist n),
  perm (unject _ (insert n e l)) (e :: unject _ l).
Proof.
intros.
funelim (insert n e l).
simp insert.
simp unject.
apply perm_skip.
apply perm_nil.
simp insert.
rewrite Heq.
simpl.
simp unject.
apply perm_refl.
simp insert.
rewrite Heq.
simpl.
simp unject.
apply perm_trans with (l2 := h :: e :: unject _ tl0).
apply perm_skip.
apply H.
apply perm_swap.
Qed.

Lemma sort_permutation : forall (n : nat) (l : ilist n),
  perm (unject _ (sort n l)) (unject _ l).
Proof.
intros.
funelim (sort n l).
simp unject.
simp sort.
simp unject.
apply perm_refl.
apply perm_trans with (l2 := h :: unject n0  (sort n0 tl0) ).
simp sort.
apply insert_permutation.
simp unject.
apply perm_skip.
apply H.
Qed.


Check length'_equation_2.
Lemma unject_inject : forall (l : list nat),
  unject _ (inject l) = l.
Proof.
intro.
funelim (inject l).

reflexivity.
simpl.
simp inject.
simp unject.
simp length'.

cbn [length'].
simp unject.
rewrite H.
reflexivity.
Qed.
Lemma inject_unject : forall (n : nat) (l : ilist n),
    unject _ (inject (unject n l)) = unject n l.
Proof.
intros.
funelim (unject n l).
simp unject.
reflexivity.
rewrite unject_inject.
reflexivity.
Qed.

End IList.
