Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.

Definition even (n: nat) := exists k, n = 2 * k.
Definition odd  (n: nat) := exists k, n = 2 * k + 1.


Axiom classic : forall P:Prop, P \/ ~ P.

Theorem	easy:	forall	(p	q:	Prop),
p	->	((p->q)	->	p). (*Question 1*)
Proof.
intro p.
intro q.
intro p_lhs.
firstorder.
Qed.

Theorem	Conversion:	forall	(p	q:	Prop),
(p	->	q)	->	(~	p	\/	q). (*Question 2*)
Proof.
intros p q.
intros p_implies_q.
destruct (classic p) as [p_true | p_false].
pose (p_implies_q p_true) as l.
right.
exact l.
left.
exact p_false.
Qed.

Theorem	NotNotAImpA	:	forall	A:	Prop,	~~A	->		A.  (*Question 3*)
Proof.
intro A.
intro double_neg.
destruct (classic A) as [p_true | p_false].
exact p_true.
contradiction.
Qed.

Theorem	PeirceContra:	forall	(p	q:Prop),
~	p	->	~((p		->	q)		->	p). (*Question 4*)
Proof.
intro p.
intro q.
intro H.
destruct (classic p) as [p_true | p_false].
intro r.
pose(H p_true)as d.
exact d.
intro k.
apply H.
intuition.
Qed.

Theorem	Peirce:	forall	(p	q:	Prop),
((p	->	q)	->	p)	->	p. (*Question 5*)
Proof.
intro p.
intro q.
intro r.
destruct (classic p) as [p_true | p_false].
exact p_true.
firstorder.
Qed.














