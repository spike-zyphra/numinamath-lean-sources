import Mathlib

theorem algebra_187691 (n : ℕ) (S : ℤ) (hS : S = ∑ i in Finset.range n, (-1 : ℤ)^i * (i + 1)) :
    Even n → S = -n / 2 ∧ Odd n → S = (n + 1) / 2 := by
  intro h_even h_contra
  have h1 : ¬ Odd n := by
    exact Nat.not_odd_iff_even.mpr h_even
  have h2 : Odd n := by
    exact h_contra.right
  contradiction