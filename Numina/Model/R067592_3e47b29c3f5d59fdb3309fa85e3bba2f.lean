import Mathlib

theorem number_theory_200973 (a : ℚ → ℤ) :
    ∃ x y, x ≤ y ∧ a x + a y ≤ 2 * a ((x + y) / 2) := by 
  use (0 : ℚ), (0 : ℚ)
  constructor
  · -- Show that (0 : ℚ) ≤ (0 : ℚ)
    norm_num
  · -- Show that a 0 + a 0 ≤ 2 * a ((0 + 0) / 2)
    have h1 : ((0 + 0) / 2 : ℚ) = (0 : ℚ) := by 
      norm_num
    rw [h1]
    linarith