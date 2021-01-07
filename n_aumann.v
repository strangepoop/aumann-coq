(**

Say we need to meet. I decide to call you to a cafe nearby, so I
send you a text that I've started.

When you see the text, you know that I've left for the cafe.

When you send back an "okay" and you see the okay marked *read*,
you know that (I've seen your okay message), ie
you know that (I know that you've seen my text about leaving), ie
you know that (I know that (you know that (I've left for the cafe))).

So this is usually enough for most people to meet, but can we nitpick? Is there
 any reason we might fail to meet anyway?

Well, you might wonder whether I know that you've seen the "okay" message.
You've seen it marked *read*, but I have no way of knowing it.

So you think about my position; you reason that I don't know whether you've seen it.
 Which means that I **don't** know that last statement above. That is,
 since I don't know that, I would reason that perhaps
 you don't know that I've seen your okay message. What would I then think about you?
 I would assume it is possible that you think that I don't know that you've seen my 
 text about leaving.
And so on.

In other words, with a finite level of I know-You knows, each successive simulation
 of the other person's mind will cause a decrement, eventually leading to a possibility
 that one of us thinks that the other person doesn't know about the event.

A way to to better think about this is to put the people in space:
Suppose E denotes the event of me leaving for the cafe.
I is me, Y is you. Knowing (or seeing, to the right) is the symbol :>.

So when you get the text, you know that I'm leaving for the cafe, ie.
Y :> E.
When you send back an okay and see the okay marked *read*,
Y :> (I :> (Y :> E)).

This isn't sufficient to meet, because when you try to think from my persepctive, there's only:
I :> (Y :> E).
which means that if you try to think about how I'd think about your persepctive, there's only:
Y :> E.
which means that if you try to think about how I'd think about how you'd think, there's only:
E.

In other words, it's imaginable to you that it's imaginable to me that it's imaginable to you
 that it's imaginable to me that you haven't received the message.

Only if it's completely unimaginable to either of us that when we run the imagining,
 neither of us will bottom out at "haven't received the message", will we
 decide to meet.

Since imagining causes a sort of decrement, we need a fixed point of the decrement operation.
ie an x s.t. dec(x) = x <-> (x - 1) = \implies x = \infty.

We need "common knowledge". In practice, this means that we need the infinite set of
 all finite successions. (???)

**)

From Coq Require Import Lists.List.
From Coq Require Import Arith.Even.
Import ListNotations.

Inductive State.

Definition Event := State -> Prop.
Notation "[ a ]" := (fun x => if x = a then True else False).
Definition implies (A B : Event) : Prop := forall (x : State), A x -> B x.
Notation "a ~> b"  := (implies a b)                   (at level 60, right associativity).
Notation "a <~> b" := (implies a b /\ implies b a)    (at level 60, right associativity).


(*** Pertison = Person that is a partition ***)
Definition intersect A B := exists w : State, A w /\  B w.
Definition func_is_partition (f : State -> State -> Prop) : Prop := 
(forall w, f w w) /\ (forall w w', f w w' -> f w' w) /\ (
forall v w x, f v w -> f w x -> f v x).
Inductive Pertison : Type := | introPertison (f : State -> Event) (prf : func_is_partition f).
Definition pertison (P : Pertison) := match P with | introPertison f _ => f end.
Definition pertison_prf (P : Pertison) : (func_is_partition (pertison P)) := match P with | introPertison f prf => prf end.

Remark per_refl : forall P w, pertison P w w.
Proof. intros. destruct P. unfold pertison.
destruct prf as [Hr [Hs Ht]]. intuition. Qed.

Remark per_symm : forall P v w, pertison P v w <-> pertison P w v.
Proof. intros. destruct P. unfold pertison.
destruct prf as [Hr [Hs Ht]]. intuition. Qed.

Remark per_tran : forall P v w x, pertison P v w -> pertison P w x -> pertison P v x.
Proof. intros. destruct P. unfold pertison in *.
destruct prf as [Hr [Hs Ht]].
apply Ht  with (w); intuition. Qed.

(*** knows: (((A -> B) -> B) -> (A -> B) -> (A -> B) ***)
Definition knows (P : Pertison) (E : Event) (w : State) : Prop := pertison P w ~> E.
Notation "P :> E" := (knows P E)    (at level 39, right associativity).
Notation "E -/ w"  := (E w)         (at level 40, only parsing).




Example PknowsE : forall P E w,
P :> E -/ w
= pertison P w ~> E.
Proof. reflexivity. Qed.


Example PknowsQknowsE : forall P Q E w,
P :> Q :> E -/ w
= pertison P w ~> (fun w' => pertison Q w' ~> E).
Proof. reflexivity. Qed.


(*** Verify our definition is equivalent to Aumann's common-sensical ones***)
Example aumann_verify1 : forall P Q E w, P :> Q :> E -/ w
<-> (fun w' => intersect (pertison Q w') (pertison P w)) ~> E.
Proof.
intros. unfold knows. unfold intersect. unfold implies. split.
  - intros. destruct H0 as (x0, [Hx0Q Hx0P]). apply H with (x:=x0).
    assumption. apply per_symm in Hx0Q. assumption.
  - intros. apply H. exists x. split.
    apply per_symm in H1. assumption. assumption.
Qed.

Example aumann_verify2 : forall P Q E w, P :> Q :> P :> E -/ w
<->
(fun w'' => intersect (pertison P w'')
 (fun w' => intersect (pertison Q w')
                      (pertison P w))) ~> E.
Proof.
intros. unfold knows. unfold intersect. unfold implies. split.
  - intros. destruct H0 as [w0 [HP [w1 [HQ HP']]]]. 
    eapply H. apply HP'. apply per_symm. apply HQ. apply per_symm. apply HP.
  - intros. eapply H. exists x0. split. apply per_symm. apply H2. exists x.
    split. apply per_symm. apply H1. apply H0.
Qed.



(*
E = ...
C = Pknows E | PknowsQKnows C
D = Qknows E | PknowsQknows C
F = C | D.
*)

(** Define CK in three ways: P knows Q knows ...; Aumann's "contains all those that intersect"
and Aumann's reachablility **)
Fixpoint CK_holds_side (c : nat) (P : Pertison) (Q : Pertison) (E : Event) : Event :=
match c with
| O   => P :> E
| S c' => (CK_holds_side c' Q P (P :> E))
end.

Definition CK_holds (P : Pertison) (Q : Pertison) (E : Event) (w : State) :=
forall n, CK_holds_side n P Q E w /\ CK_holds_side n Q P E w.

Fixpoint CK_intersecty (c : nat) (P : Pertison) (Q : Pertison) (w : State) : Event :=
match c with
| O => pertison P w
| S c' => (fun w' => intersect (pertison P w') (CK_intersecty c' Q P w))
end.

Fixpoint reachable (l : list State) (P : Pertison) (Q : Pertison)
(w : State) (v : State) : Prop :=
match l with 
| [] => pertison P w v
| (h::l') => pertison P h v /\ reachable l' Q P w h
end.

(** Some remarks about reachable that'll help prove equivalances **)
Remark reachable_end : forall l P Q w v t,
reachable (l ++ [t]) P Q w v <->
(even (length l) ->
reachable l P Q t v /\ pertison Q w t) /\
(odd (length l) ->
reachable l P Q t v /\ pertison P w t).
Proof.
induction l.
- intros. rewrite app_nil_l. unfold reachable. fold reachable.
  split.
  + split. intros. assumption. intros. inversion H0.
  + intros [H H']. apply H. apply even_O.
- intros. rewrite <-app_comm_cons. unfold reachable. fold reachable.
  replace (length (a :: l)) with (S (length l)).
  split.
  + intros [HP Hr]. apply IHl in Hr. destruct Hr as [Hre Hro].
    split.
    * intros. apply and_assoc. split. assumption.
      apply Hro. inversion H. assumption.
    * intros. apply and_assoc. split. assumption.
      apply Hre. inversion H. assumption.
  + intros [He Ho].
    assert (even (S (length l)) \/ odd (S (length l))) by apply even_or_odd.
    assert (distr_and : forall A B C D, (A -> (B /\ C) /\ D) <->
    ((A -> B) /\ (A -> C) /\ (A -> D))) by tauto.
    apply distr_and in He. destruct He as [HeP [HeR HeQ]].
    apply distr_and in Ho. destruct Ho as [HoP [HoR HoQ]].
    inversion H.
    * split.
      apply HeP. assumption.
      apply IHl. split. 
      { intros. exfalso. apply not_even_and_odd with (S (length l)).
        assumption. apply odd_S. assumption. }
      { intros. split. apply HeR. assumption. apply HeQ. assumption. }
    * split.
      apply HoP. assumption.
      apply IHl. split.
      { intros. split. apply HoR. assumption. apply HoQ. assumption. }
      { intros. exfalso. apply not_even_and_odd with (S (length l)).
        apply even_S. assumption. assumption. }
  + replace (a :: l) with ([a] ++ l). rewrite app_length.
    replace (length [a]) with 1. reflexivity. reflexivity. reflexivity.
Qed.

Lemma reachable_rev_eo : forall l P Q w w',
reachable l P Q w w' ->
(even (length l) -> reachable (rev l) P Q w' w) /\
(odd  (length l) -> reachable (rev l) Q P w' w).
Proof.
induction l.
- unfold rev. unfold reachable. unfold length.
  intros. split; intros. apply per_symm. assumption.
  exfalso. apply not_even_and_odd with 0. apply even_O. assumption.
- assert (Heqn : even (length l) \/ odd (length l)) by apply even_or_odd.
  intros. replace (rev (a::l)) with (rev l ++ [a]).
  inversion Heqn; split; intros;
  destruct H as [HP Hr].
  + exfalso. apply not_even_and_odd with (length l).
    assumption. unfold length in H1. fold length in H1.
    inversion H1. assumption.
  + apply reachable_end. split.
    * apply IHl in Hr. rewrite rev_length. destruct Hr as [Hre Hro].
    intros; split. apply Hre. assumption.
    apply per_symm. assumption.
    * intros; split.
    exfalso. apply not_even_and_odd with (length l).
    unfold length in H1. fold length in H1. inversion H1.
    assumption. rewrite rev_length in H. assumption.
    exfalso. apply not_even_and_odd with (length l).
    unfold length in H1. fold length in H1. inversion H1.
    assumption. rewrite rev_length in H. assumption.
  + apply reachable_end. split.
    * intros; split.
    exfalso. apply not_even_and_odd with (length l).
    unfold length in H1. fold length in H1. inversion H1.
    rewrite rev_length in H. assumption. assumption.
    exfalso. apply not_even_and_odd with (length l).
    unfold length in H1. fold length in H1. inversion H1.
    rewrite rev_length in H. assumption. assumption.
    * apply IHl in Hr. rewrite rev_length. destruct Hr as [Hre Hro].
    intros; split. apply Hro. assumption.
    apply per_symm. assumption.
  + exfalso. apply not_even_and_odd with (length l).
    unfold length in H1. fold length in H1.
    inversion H1. assumption. assumption.
  + replace (a::l) with ([a] ++ l). reflexivity. reflexivity.
Qed.

Remark reachable_rev : forall l P Q w w',
reachable l P Q w w' -> exists m, reachable m P Q w' w.
Proof.
intros. apply reachable_rev_eo in H. destruct H as [He Ho].
assert (Heqn : even (length l) \/ odd (length l)) by apply even_or_odd.
inversion Heqn.
- exists (rev l). tauto.
- exists (w::rev l). unfold reachable. fold reachable.
  split. apply per_refl. tauto.
Qed.

Lemma reachable_switch : forall l P Q w v, reachable l P Q w v <-> reachable (v::l) Q P w v.
Proof.
split; intros.
- unfold reachable. fold reachable. split. apply per_refl. tauto.
- unfold reachable in H. fold reachable in H. tauto.
Qed.

Lemma reachable_app_omit : forall l1 l2 P Q w v x,
reachable (l1 ++ (x::x::l2)) P Q w v -> reachable (l1 ++ l2) P Q w v.
Proof.
induction l1; intros.
- rewrite app_nil_l in *. unfold reachable in *.  fold reachable in *.
  destruct l2. unfold reachable in *.
  apply per_tran with (w:=x); tauto. unfold reachable in *. fold reachable in *.
  split. apply per_tran with (w:=x); tauto. tauto.
- rewrite <-app_comm_cons. unfold reachable in *. fold reachable in *.
  inversion H. apply IHl1 in H1. tauto.
Qed.

Remark reachable_app_eo : forall l1 l2 P Q w v x,
reachable l2 P Q w x -> reachable l1 P Q x v ->
(even (length l1) -> reachable ((l1 ++ [x]) ++ x::l2) P Q w v) /\
(odd  (length l1) -> reachable ((l1 ++ [x]) ++ l2) P Q w v).
Proof.
induction l1; split; intros.
- rewrite app_nil_l. rewrite <-app_comm_cons. 
  rewrite app_nil_l. unfold reachable in *. fold reachable in *.
  assert (pertison Q x x) by apply per_refl. tauto.
- inversion H1.
- rewrite <-app_assoc. rewrite <-app_comm_cons. 
  unfold reachable. fold reachable.
  inversion H0. split. tauto.
  inversion H1. apply reachable_switch in H.
  rewrite app_assoc.
  apply IHl1 with (v:=a); tauto.
- rewrite <-app_assoc. rewrite <-app_comm_cons.
  unfold reachable. fold reachable.
  inversion H0. split. tauto.
  inversion H1. apply reachable_switch in H.
  apply IHl1 with (v:=a) in H. apply H in H5.
  apply reachable_app_omit in H5.
  rewrite app_assoc. tauto. tauto.
Qed.

Remark reachable_app : forall l2 l1 P Q w v x,
reachable l2 P Q w x -> reachable l1 P Q x v ->
exists l, reachable l P Q w v.
Proof.
intros. apply reachable_app_eo with (l2:=l2)(w:=w) in H0.
assert (even (length l1) \/ odd (length l1)) by apply even_or_odd.
inversion H0. inversion H1. 
exists ((l1 ++ [x]) ++ x::l2). tauto.
exists ((l1 ++ [x]) ++ l2). tauto. tauto.
Qed.

Lemma reachable_implies_intersecty : forall l P Q w v,
reachable l P Q w v ->
CK_intersecty (length l) P Q w v.
Proof.
induction l.
- intros. unfold length. unfold CK_intersecty. unfold reachable. intuition.
- intros P Q w v [HP Hrest]. apply IHl in Hrest.
  (* unfold CK_intersecty. fold CK_intersecty.
  unfold intersect. *) exists a. split.
  apply per_symm. assumption. assumption.
Qed.

Lemma intersecty_implies_reachable : forall n P Q w v,
CK_intersecty n P Q w v ->
(exists l, reachable l P Q w v).
Proof.
induction n.
- intros. exists []. assumption.
- intros. unfold CK_intersecty in H. fold CK_intersecty in H.
  unfold intersect in H. destruct H as [h [HP Hint]].
  apply IHn in Hint. destruct Hint as [l Hrest].
  exists (h::l). unfold reachable. fold reachable. split.
  apply per_symm. assumption. assumption.
Qed.

Remark intersecty_is_reachable : forall P Q w v,
(exists n, CK_intersecty n P Q w v) <->
(exists l, reachable l P Q w v).
Proof.
intros. split.
intros [n H]. apply intersecty_implies_reachable in H. assumption.
intros [l H]. exists (length l). apply reachable_implies_intersecty in H. assumption.
Qed.

Lemma intersect_succ : forall n P Q E w,
CK_intersecty n Q P w ~> P :> E <->
CK_intersecty (S n) P Q w ~> E.
Proof.
intros. split.
- unfold CK_intersecty. fold CK_intersecty. 
  unfold knows in *. unfold implies in *. unfold intersect in *.
  intros. destruct H0 as [v [HP Hint]].
  apply H with (v). assumption. apply per_symm. assumption.
- unfold CK_intersecty. fold CK_intersecty. 
  unfold knows in *. unfold implies in *. unfold intersect in *.
  intros. apply H. exists x. split. apply per_symm. assumption. assumption.
Qed.

Theorem aumann_same : forall n P Q E w, CK_holds_side n P Q E w <->
CK_intersecty n P Q w ~> E.
Proof.
induction n.
- intuition.
- intros. split.
  + intros. apply intersect_succ.
    unfold CK_holds_side in H. fold CK_holds_side in H.
    apply IHn with (Q)(P)(P :> E)(w) in H.
    assumption.
  + intros. apply IHn.
    unfold CK_intersecty. fold CK_intersecty.
    apply intersect_succ in H. assumption.
Qed.


Definition meet_f (P Q : Pertison) : State -> Event :=
(fun w => fun v => exists l, reachable l P Q w v).

Remark meet_prf : forall P Q, func_is_partition(meet_f P Q).
Proof.
intros. unfold func_is_partition. split; intros.
- unfold meet_f. exists []. unfold reachable. apply per_refl.
- split; intros. unfold meet_f in *. destruct H as [l H].
  apply reachable_rev in H. tauto.
+ unfold meet_f in *. destruct H as [l1 H]. destruct H0 as [l2 H']. 
  apply reachable_app with (l1)(l2)(w). tauto. tauto.
Qed.

Definition meet (P Q : Pertison) : Pertison := 
introPertison (meet_f P Q) (meet_prf P Q).

Remark meet_symm : forall P Q w v, pertison (meet P Q) w v <-> pertison (meet Q P) w v.
Proof. intros. unfold pertison. split; intros; destruct H as [l H];
exists (v::l); apply reachable_switch in H; tauto. Qed.


(** This might look reversed, but that's because (?) it's contravariant on the prop **)
Remark meet_coarser : forall P Q w,
pertison P w ~> pertison (meet P Q) w.
Proof.
intros. unfold implies. intros. destruct P.
exists []. assumption.
Qed.

Theorem meet_is_CK : forall P Q E w,
CK_holds P Q E w <-> 
pertison (meet P Q) w ~> E.
Proof.
split; intros.
- unfold implies. unfold pertison; unfold meet; unfold meet_f. intros.
  destruct H0 as [l Hr].  unfold CK_holds in *.
  assert (CK_holds_side (length l) P Q E w) by apply H. apply aumann_same in H0.
  apply H0. apply reachable_implies_intersecty. tauto.
- assert (H' : pertison (meet Q P) w ~> E).
  { unfold implies. intros. apply H. apply meet_symm. tauto. }
  unfold CK_holds. unfold implies in *; unfold pertison in *; 
  unfold meet in *; unfold meet_f in *.
  induction n.
  + split; apply aumann_same; unfold implies;
    intros; apply intersecty_implies_reachable in H0.
    apply H.  tauto.
    apply H'. tauto.
  + split; apply aumann_same; unfold implies; 
    destruct IHn as [IHnP IHnQ];
    apply aumann_same in IHnP; apply aumann_same in IHnQ;
    intros; apply intersecty_implies_reachable in H0.
    apply H.  tauto.
    apply H'. tauto.
Qed.


Definition disjoint (P : Event -> Prop) : Prop :=
forall E F v, P E -> P F -> E v -> F v -> (E <~> F).

Definition distinct_class (P : Pertison) (E : Event) : Prop := 
forall v w, E v -> E w -> pertison P v w -> v = w.

(* nub all the omega in an event until they are distinct, modulo P *)
Definition nub_class (P : Pertison) (E : Event) : Event. Admitted.
Remark nub_works : forall P E, distinct_class P (nub_class P E). Admitted.

(** Any member of meet P Q is built of some collection of disjoint members of P 
The collection is indexed by some v's, whose classes v-bar we'll union. **)


(* Is there a way to say, once I have this, I can nub it, and retain this property? *)
Remark meet_part : forall P Q w, exists vs : (State -> Prop),
(forall x : State, pertison (meet P Q) w x <->
(exists v, vs v /\ pertison P v x)).
Proof.
intros. exists (fun a => pertison (meet P Q) w a).
split; intros.
- exists x. split. assumption. destruct P. destruct prf as [H0 H1]. apply H0.
- destruct H as [v [Hm HP]]. apply meet_coarser with (P)(Q)(v) in HP.
  apply per_tran with (w:=v); tauto.
Qed.


(*
(*Remark meet_universal forall P Q w*)
Definition countable_union_over_pertison (P : Pertison) (f : nat -> State) (w : State) : Prop := 
exists n, pertison P (f n) w.

Definition meet_indexer (P Q : Pertison) (w : State) (n : nat) : Event :=
(fffun v => CK_intersecty n P Q w v /\ CK_intersecty n Q P w v).
(* no no no, should come partitio + coarsening.*)
Lemma meet_projl : forall P Q w,
exists f, forall v, pertison (meet P Q) w v <-> 
countable_union_over_pertison P f v.
Proof.
*)
(** finite :( 
Fixpoint join_from (n : nat) (f : nat -> Event) (w : State) : Prop :=
match n with
| O => f O w
| S m => f (S m) w \/ join_from m f w
end.
**)




(** Huh? So given any obtained state of the world,
this is just a math statment? Are we dealing with
logical uncertainty here?! I'm not even sure how
Aumann is defining this type of event. Is it the
outcome that results in a proof of such statement?
Definition propevent (prop : Prop) : Event := (fun _ => prop).**)


(** Best to wrap these up as one conditional called
probability_facts and then use them in the theorem.
That they are true of probability theory is left unproven. ***)

(* whatever representation of the raw probailities *)
Inductive Prob_raw.
(** Dividing doesn't yield prbabilities, so this must be replaced by atomic posterior **)
Inductive Prob :=
| ret : Prob_raw -> Prob
| mul : Prob -> Prob -> Prob
| div : Prob -> Prob -> Prob.

(** assumes no division by zero! ("non-null" is in the paper) **)
Definition mul_div_inverse : Prop := 
forall x y, mul y (div x y) = x.

Definition mul_cancel : Prop :=
forall x y z, mul x z = mul y z -> x = y.
(*** Proof. intros.
replace (mul x z) with (mul x (div z x)) in H0.
replace (mul y z) with (mul y (div y x)) in H0.
rewrite H in H0. Admitted.***)


Definition prior (P : Pertison) (E : Event) : Prob. Admitted.

(*** Read as posterior p ( E | P ) ***)
Definition posterior (p : Event -> Prob) (E : Event) (P : Pertison) (w : State) : Prob :=
let PE := pertison P w in div (p (fun v => E v /\ PE v)) (p PE).

(** notation hack because I couldn't get multi-notation to work **)
Notation "f '{{' x '}}'" := (posterior f (fst x) (snd x))     (at level 60)(*, only parsing*).
Notation "b '/' c" := (b,c)                     (*(at level 40) only parsing *).

Definition ee : Event. Admitted.
Definition pp : Pertison. Admitted.
Check (prior pp) {{ ee / pp }}.

Definition equals_event {X} (f : State -> X) (a : X) (w : State) : Prop := f w = a.
Notation "f ~= a" := (equals_event f a)             (at level 61).


(**Definition nonempty_part (P : Event -> Prop) : Prop := exists (w : State) **)


Definition fines_fst (P Q : Pertison) (w : State) : Event -> Prop :=
fun E => (exists v, E <~> pertison P v) /\ E ~> pertison (meet P Q) w.
Definition fines_snd (P Q : Pertison) (w : State) : Event -> Prop :=
fun E => (exists v, E <~> pertison Q v) /\ E ~> pertison (meet P Q) w.

(** IMPORTANT: replace these with just mutual sum rule of probability, then derive using fines_fst above **)
Definition sum_rule_fst : Prop := forall (P Q : Pertison) (E : Event)
(p : Event -> Prob) (q : Prob) (w : State),
( forall v, pertison (meet P Q) w v ->  (** any state v in the w-class of the join **)
 (p{{E/P}} ~= q) v ) ->       (** the P-conditional probability is q throughout **)
p (fun v => E v /\ pertison (meet P Q) w v) = mul q (p (pertison (meet P Q) w)).

Definition sum_rule_snd : Prop := forall (P Q : Pertison) (E : Event)
(p : Event -> Prob) (q : Prob) (w : State),
(forall v, pertison (meet P Q) w v ->  (** any state v in the w-class of the join **)
(p{{E/Q}} ~= q) v ) ->       (** the Q-conditional probability is q throughout **)
p (fun v => E v /\ pertison (meet P Q) w v) = mul q (p (pertison (meet P Q) w)).

Definition sum_rules := sum_rule_fst /\ sum_rule_snd.

Definition mutex_exhaust_cover {X} (A : X -> Event) (B : Event) : Prop :=
(forall (v : State), B v -> exists i, A i v) /\ 
(forall (i j : X) (v : State), A i v -> A j v -> (forall x, A i x <-> A j x)).
Notation "A #> B" := (mutex_exhaust_cover A B) (at level 60).

Remark meet_cover : forall P Q w,
(pertison P) #> (pertison (meet P Q) w).
Proof. unfold mutex_exhaust_cover.
split; intros.
- exists v. apply per_refl.
- apply per_symm in H. apply per_tran with (v:=j) in H.
  split; intros.
  + apply per_tran with (w:=i); assumption.
  + apply per_symm in H. apply per_tran with (w:=j); assumption.
  + assumption.
Qed.

Axiom sum_rule : forall A B p, 
A #> B ->
(forall x, p (A x) = q) -> [AHHHH FIRST (*MAKE*) MUTEX_EXHAUST better.]

Theorem jze : sum_rule_fst.
Proof.
unfold sum_rule_fst. intros. unfold posterior in *. unfold fst in *. unfold snd in *.
unfold equals_event in *.

forall v, B v -> p (fun v0 : State => E v0 /\ Av v0) = mul q (p Av)
then               (fun v0 : State => E v0 /\ B  v0) = mul q (p B)
where B = (pertison (meet P Q) w)
      Av = pertison P v.
OR:
forall v, B v -> p(E|Av) = q
then             p(E|B)  = q
(if Av spans B and are mutually exclusive.)
(ie if B x -> exists v. A v x and also A y x -> A z x -> A y z)

The above follows from
forall v, B v -> p(Av) = q
then             p(B)  = q
(if ...)

and the fact that intersection doesn't change anything, ie:
forall v, B v -> p(Av `inters` E)  = q
then             p(B  `inters` E)  = q
by dividing (carefully!) on both sides.


Need:
part_intersect : A parts B -> forall E, (A `(map of)int` E) parts (B `int` E)
sum rule : A parts B -> p(B) = c ->

(**
Definition sum_rule : Prop := forall (A B : Pertison) (Ai E : Event) 
(p : Event -> Prob) (pa : Prob) (w : State),
nub_class A Ai w ->
(p{{E/A}} ~= pa) w ->
(*A paritions  (meet A B) w ->*)
p (fun v => E v /\ C v) = pa.

(* Is this right? this looks wrong. *)
Definition sum_rule (C : Event -> Prop) : Prop := forall (A B : Pertison) (E : Event) (p : Event -> Prob) (pa : Prob) (w : State), 
C w ->
(p{{E/A}} ~= pa) w ->
(*A paritions  (meet A B) w ->*)
p (fun v => E v /\ C v) = pa.
(** ie p{{E/A}} times p (A w)  is pa. **)
**)

Definition posterior_equals (pri : Event -> Prob) (A: Event) (P : Pertison)
(p : Prob) (w : State) :=
posterior pri A P w = p.

(** Just to show no need for awkward posterior_equals **)
Example choo: forall (p : Event -> Prob) (A: Event) (P : Pertison)
(p1 : Prob) (w : State),
(posterior_equals p A P p1) w
<->
( p{{A/P}} ~= p1) w.
Proof. tauto. Qed.

(***
Suppose for some v, x(v) = y(v) is CK at w.
The inner expression has nothing to do with w.
But how do I represent it as an event? 
What are all the w for which it's true?

If v happens to be w, is the correct way 
to mark all those w for which x(w) = y(w)?
That sounds very very wrong.

And I seem to disagree with the proof in the paper!
Aumann very much seems to be saying that
if some proposition B(w) becomes common knowledge at w, then
B(v) is true for all v in the PmeetQ class of w.
This is his line ("since \bold{q_1} = q1 throughout P, ..." where the
ellipsis is then done for *each* v in the PmeetQ class of w.

I guess I'm still not clear about what it means for a propositional event
to hold at w? Interestingly, the way I've defined it below might also lead
to the same thing as Aumann, but I feel like I'm making a mistake.
***)


(** need something like this 
Axiom marginalize : forall (A_i : NubbedParitioningList) (X : IntersectWith A_i) (A : A_i),
mult p{{X/A}} p(A) = p (intersection X A).

nubclass A (fun z => exists x, pertison (meet A B) w x /\ pertison A x z
**)


Theorem aumann_agreement:
forall (A : Pertison) (B : Pertison) (E : Event) (w : State) (p : Event -> Prob) (pa pb : Prob),
sum_rules /\ mul_cancel-> (* basic arithmetic/probability results *)
prior A = p ->
prior B = p ->
CK_holds A B ( p{{E/A}} ~= pa ) w ->
CK_holds A B ( p{{E/B}} ~= pb ) w ->
pa = pb.
Proof.
intros.
apply meet_is_CK in H2. apply meet_is_CK in H3.
unfold implies in *. unfold equals_event in *.
apply H in H2. apply H in H3.
rewrite H3 in H2.
apply H in H2. symmetry. assumption.
Qed.

