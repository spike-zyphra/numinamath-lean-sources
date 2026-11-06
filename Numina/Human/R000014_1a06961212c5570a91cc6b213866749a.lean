import Mathlib

/- Let $(G, 0, +)$ be a commutative group with cardinality $k$. Show that for every element $x$ in $G$, we have $k x = 0$.-/
theorem algebra_4026 {G : Type*} [AddCommGroup G] [Fintype G] :
    ∀ x : G, Fintype.card G • x = 0 := by
  -- exact `card_nsmul_eq_zero` in Mathlib
  intro x
  exact card_nsmul_eq_zero
