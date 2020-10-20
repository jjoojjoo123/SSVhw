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
Hypothesis Associativity : forall a, forall b, forall c, (a ` (b ` c) = (a ` b) ` c).
Hypothesis Identity : forall a, ((a ` e = a) /\ (e ` a = a)).
Hypothesis Inverse : forall a, (exists b, ((a ` b = e) /\ (b ` a = e))).

Section three_a.

Lemma l5 : forall a, forall b, forall c, ((a ` b = a ` c) -> b = c).
Proof.
intro x.
intro y.
intro z.
intro w.

elim (Identity z).
intro u.
intro v.
rewrite <- v.

elim (Inverse x).
intro x_inv.
intro subInv.
elim subInv.
intro n.
intro m.
rewrite <- m.

rewrite <- (Associativity x_inv x z).
rewrite <- w.

rewrite (Associativity x_inv x y).
rewrite m.

elim (Identity y).
intro p.
intro q.
rewrite q.
reflexivity.
Qed.

End three_a.


Section three_b.

Lemma l6 : forall a, forall b, forall c, (((a ` b = e) /\ (b ` a = e) /\ (a ` c = e) /\ (c ` a = e)) -> b = c).
Proof.
intro x.
intro y.
intro z.
intro w.
elim (Identity y).
intro u.
intro v.
rewrite <- u.

elim w.
intro i.
intro j.
elim j.
intro k.
intro l.
elim l.
intro m.
intro n.
rewrite <- m.

rewrite (Associativity y x z).
rewrite k.

elim (Identity z).
intro p.
intro q.
rewrite q.
reflexivity.
Qed.

End three_b.