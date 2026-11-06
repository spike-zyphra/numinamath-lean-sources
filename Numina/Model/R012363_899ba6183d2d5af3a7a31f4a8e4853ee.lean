import Mathlib

theorem number_theory_3456 (f : ℤ × ℤ → ℤ) (n : ℤ) :
    ∃ a b c d : ℤ, (b - a = d - c) ∧ (n ∣ ∑ i in Finset.Icc a b, ∑ j in Finset.Icc c d, f (i, j)) := by
  use 1, 0, 1, 0
  constructor
  · -- Show that b - a = d - c
    norm_num
  · -- Show that n divides the sum
    simp [Finset.sum_eq_zero]