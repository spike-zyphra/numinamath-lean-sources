import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_233536 (a : ℝ) : sqrt (a^2 + 1) + sqrt 2 > |a + 1| := by
  have h1 : sqrt (a^2 + 1) ≥ |a| := by
    cases' abs_cases a with ha ha
    · -- Assume a ≥ 0, so |a| = a
      have h2 : a ^ 2 + 1 ≥ a ^ 2 := by linarith [show (1 : ℝ) ≥ 0 by norm_num]
      have h3 : sqrt (a ^ 2 + 1) ≥ sqrt (a ^ 2) := Real.sqrt_le_sqrt (h2)
      have h4 : sqrt (a ^ 2) = a := Real.sqrt_sq (show 0 ≤ a by linarith)
      rw [h4] at h3
      linarith
    · -- Assume a < 0, so |a| = -a
      have h2 : a ^ 2 + 1 ≥ a ^ 2 := by linarith [show (1 : ℝ) ≥ 0 by norm_num]
      have h3 : sqrt (a ^ 2 + 1) ≥ sqrt (a ^ 2) := Real.sqrt_le_sqrt (h2)
      have h4 : sqrt (a ^ 2) = -a := by
        have h5 : a < 0 := by linarith
        have h6 : sqrt (a ^ 2) = |a| := by
          rw [Real.sqrt_sq_eq_abs]
        rw [h6]
        rw [abs_of_neg h5]
        all_goals linarith
      rw [h4] at h3
      linarith
  have h2 : sqrt (2 : ℝ) > 1 := by
    have h1 : (1 : ℝ) ^ 2 < (2 : ℝ) := by norm_num
    have h2 : (1 : ℝ) < sqrt (2 : ℝ) := by
      rw [Real.lt_sqrt] <;> nlinarith
    linarith [h2]
  have h3 : sqrt (a^2 + 1) + sqrt 2 > |a + 1| := by
    have h4 : sqrt (a ^ 2 + 1) ≥ |a| := h1
    have h5 : |a + 1| ≤ |a| + 1 := by
      cases' abs_cases (a + 1) with h1 h1
      · -- Assume a + 1 ≥ 0, so |a + 1| = a + 1
        cases' abs_cases a with h2 h2
        · -- Assume a ≥ 0, so |a| = a
          linarith
        · -- Assume a < 0, so |a| = -a
          linarith
      · -- Assume a + 1 < 0, so |a + 1| = - (a + 1)
        cases' abs_cases a with h2 h2
        · -- Assume a ≥ 0, so |a| = a
          linarith
        · -- Assume a < 0, so |a| = -a
          linarith
    have h6 : sqrt (2 : ℝ) > 1 := h2
    have h7 : sqrt (a ^ 2 + 1) + sqrt 2 ≥ |a| + sqrt 2 := by
      linarith [h4]
    have h8 : |a| + sqrt 2 > |a + 1| := by
      have h9 : |a + 1| ≤ |a| + 1 := h5
      have h12 : sqrt (2 : ℝ) > 1 := h2
      linarith [h9, h12]
    linarith [h7, h8]
  exact h3