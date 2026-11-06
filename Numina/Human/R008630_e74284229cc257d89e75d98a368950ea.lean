import Mathlib

/-Suppose we have 2 fair 6-sided dice numbered from 1 to 6.  If we roll them both, what is the probability that the two numbers shown sum to 7?-/
theorem algebra_21321 :(Finset.card {(x, y) : Finset.Icc 1 6 × Finset.Icc 1 6 | x.1 + y.1 = 7}) / (36 : ℝ) = 1 / 6 := by
  -- just to prove the card of the set is 6.
  suffices Finset.card {(x, y) : Finset.Icc 1 6 × Finset.Icc 1 6 | x.1 + y.1 = 7} = 6 by
    field_simp [this]
    linarith
  simp
  exact rfl