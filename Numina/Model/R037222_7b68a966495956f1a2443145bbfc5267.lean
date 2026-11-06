import Mathlib

open Real

theorem number_theory_311325 {n : ℚ} (hn : n > 0) :
    ∃ k l, n = 2 * sqrt (k * k + l) ∧ k > 0 ∧ l > 0 := by 
  use (n / 4)
  use (3 * n ^ 2 / 16)
  have h1 : (n / 4 : ℝ) > 0 := by
    exact_mod_cast (show (n / 4 : ℚ) > 0 by
      linarith
    )
  have h2 : (3 * n ^ 2 / 16 : ℝ) > 0 := by
    exact_mod_cast (show (3 * n ^ 2 / 16 : ℚ) > 0 by
      nlinarith [sq_pos_of_pos hn]
    )
  have h3 : (n : ℝ) = (2 * Real.sqrt ((n / 4 : ℝ) * (n / 4 : ℝ) + (3 * n ^ 2 / 16 : ℝ)) : ℝ) := by
    have h4 : Real.sqrt ((n / 4 : ℝ) * (n / 4 : ℝ) + (3 * n ^ 2 / 16 : ℝ)) = (n / 2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [sq_pos_of_pos hn]
    rw [h4]
    all_goals linarith
  constructor
  · -- Show n = 2 * sqrt((n / 4) ^ 2 + (3 * n ^ 2 / 16))
    exact_mod_cast h3
  constructor
  · -- Show k > 0
    exact_mod_cast h1
  · -- Show l > 0
    exact_mod_cast h2