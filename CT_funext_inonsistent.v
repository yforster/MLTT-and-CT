Require Import PeanoNat Lia.

(*
  We assume a function compute such that
    compute n c x
  computes the c-th Turing machine on input x for n steps,
  and returns 0 if the machine does not halt and 1 + r if it halts with result r.
 *)
Axiom compute : nat -> nat -> nat -> nat.

(*
  If a machine halts after n1 steps and after n2 steps, then compute yields the same result.
*)
Axiom computes_det : forall c x n1 n2, compute n1 c x <> 0 -> compute n2 c x <> 0 -> compute n1 c x = compute n2 c x.

(*
  We write c ~ f to indicate that the c-th Turing machine computes a function f.
*)
Notation "c ~ f" := (forall x, exists n, compute n c x = 1 + f x) (at level 50).

(*
  MLTT-style CT, which allows identifying functions with computable functions.
*)
Definition CT := 
  forall f : nat -> nat, {c | c ~ f}.

(*
  A predicate is decidable if the type of decisions is inhabited
*)
Definition dec {X} (P : X -> Prop) := inhabited (forall x, {P x} + {~P x}).

(*
  CT implies that it is undecidable to check whether the c-th Turing machine does not halt on a given input x, i.e. the complement of the halting problem is undecidable.

 We assume this to omit the technical proof.
*)
Axiom halting_undec : CT -> ~ dec (fun '(c,x) => forall n, compute n c x = 0).

(*
  The ∀Σ form of CT can equivalently be stated as the existence of a coding *function*
*)
Lemma CT_to_function : CT -> {F : (nat -> nat) -> nat | forall f, F f ~ f}.
Proof.
  intros ct. exists (fun f => proj1_sig (ct f)).
  intros f. apply proj2_sig.
Qed.

(*
  Functional extensionality implies that every higher-order function has to treat its input extensionally.
*)
Axiom extensional_inputs : forall F : (nat -> nat) -> nat, forall f g, (forall x, f x = g x) -> F f = F g.

(*
  Applying this to the coding function from above, we can decide whether a function f is constantly 0 by checking whether F f = F (fun _ => 0)
*)
Lemma CT_to_decider : CT -> dec (fun f => forall n : nat, f n = 0).
Proof.
  intros [F ct] % CT_to_function.
  econstructor. intros f.
  destruct (Nat.eqb_spec (F f) (F (fun _ => 0))).
  - left. intros n.
    destruct (ct f n) as [n1 Hn1].
    destruct (ct (fun _ => 0) n) as [n2 Hn2].
    rewrite e in Hn1. erewrite computes_det with (n2 := n1) in Hn2; eauto.
    all: lia.
  - right. intros H. eapply n, extensional_inputs, H.
Qed.

(*
  But now CT implies that we can decide whether a Turing machine does not halt on a given inout - the complement of the halting problem, which is undecidable.
*)
Lemma contradiction :
  CT -> False.
Proof.
  intros H.
  apply (halting_undec H).
  apply CT_to_decider in H as [d].

  constructor. intros [c x]. apply d.
Qed.
