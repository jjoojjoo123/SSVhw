Variable p q r: Prop.

Section one_a.
Lemma l1 : (p /\ q -> r) -> (p -> (q -> r)).

Proof.
intro x.
intro y.
intro z.
apply x.
split.
assumption.
assumption.
Qed.

End one_a.


Section one_b.
Hypothesis h : p \/ q -> r.
Lemma l2 : (p -> r) /\ (q -> r).

Proof.
split.
intro x.
apply h.
left.
assumption.
intro y.
apply h.
right.
assumption.
Qed.

End one_b.


Variable D: Set.

Section two_a.
Variables P: D -> D -> Prop.
Lemma l3 : (exists x, forall y, P x y) -> (forall y, exists x, P x y).

Proof.
intro a.
intro w.
elim a.
intro z.
intro b.
exists z.
apply b.
Qed.

End two_a.



Section two_b.
Variables P Q: D -> Prop.
Hypothesis h : forall x, (P x -> Q x).
Lemma l4 : (forall x, P x) -> (forall x, Q x).

Proof.
intro a.
intro y.
apply h.
apply a.
Qed.

End two_b.


Variable DOT: D -> D -> D.
Variable e: D.
Notation "A ` B" := (DOT A B) (at level 40, left associativity).

Section three_a.
Hypothesis Associativity : forall a, forall b, forall c, (a ` (b ` c) = (a ` b) ` c).
Hypothesis Identity : forall a, ((a ` e = a) /\ (e ` a = a)).
Hypothesis Inverse : forall a, (exists b, ((a ` b = e) /\ (b ` a = e))).

Lemma l5 : forall a, forall b, forall c, ((a ` b = a ` c) -> b = c).
Proof.
intro x.
intro y.
intro z.
intro w.
rewrite <- Identity.
Qed.

End three_a.