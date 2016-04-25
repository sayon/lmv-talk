Parameter A B C: Prop.
Definition t1 : (A -> B -> C) -> A -> B -> C.
  intros f a b.
  apply f.
  exact a.
  exact b.
Qed.
