Inductive True : Prop := T.
Inductive False : Prop := .

Inductive And (A B: Prop) :=
| join : A -> B -> And A B.

Inductive Or (A B: Prop) :=
| left : A-> Or A B
| right: B -> Or A B.
