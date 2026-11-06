import Mathlib

theorem number_theory_2798 (a : ℝ) : ⌊a⌋ > a - 1 := by
  have h2 : a < (⌊a⌋ + 1 : ℝ) := by
    exact Int.lt_floor_add_one a
  have h3 : (⌊a⌋ : ℝ) > a - 1 := by
    linarith
  exact h3