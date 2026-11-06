import Mathlib

theorem algebra_233220 (x : ℝ) (hx : x ≠ -1 ∧ x ≠ -7) (h : (x + 3) * (x + 5) = 4 + 2021 / ((x + 1) * (x + 7))) :
    x = -4 + 2 * Real.sqrt 13 ∨ x = -4 - 2 * Real.sqrt 13 := by
  have h1 : (x + 1) * (x + 7) ≠ 0 := by
    apply mul_ne_zero
    · -- x + 1 ≠ 0
      intro h2
      apply hx.1
      linarith
    · -- x + 7 ≠ 0
      intro h2
      apply hx.2
      linarith
  have h2 : (x + 3) * (x + 5) * ((x + 1) * (x + 7)) = 4 * ((x + 1) * (x + 7)) + 2021 := by
    have h_eq : (x + 3) * (x + 5) = 4 + 2021 / ((x + 1) * (x + 7)) := h
    field_simp [h1] at h_eq ⊢
    linarith [h_eq]
  have h_eq : (x + 4) ^ 2 - 52 = 0 := by
    nlinarith [sq_pos_of_ne_zero (show (x + 1) ≠ 0 by intro h2; apply hx.1; linarith),
      sq_pos_of_ne_zero (show (x + 7) ≠ 0 by intro h2; apply hx.2; linarith),
      Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num : (0 : ℝ) < 13),
      Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num : (0 : ℝ) ≤ 13)]
  have h_eq2 : (x + 4 - 2 * Real.sqrt 13) * (x + 4 + 2 * Real.sqrt 13) = 0 := by
    have h_eq1 : (x + 4) ^ 2 - 52 = 0 := h_eq
    have h_eq2 : (x + 4) ^ 2 - (52 : ℝ) = ( (x + 4) - 2 * Real.sqrt 13 ) * ( (x + 4) + 2 * Real.sqrt 13 ) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num), Real.sqrt_nonneg 13]
    rw [h_eq2] at h_eq1
    linarith
  cases' (mul_eq_zero.1 h_eq2) with h_eq3 h_eq4
  · -- case where x + 4 - 2 * sqrt 13 = 0 
    left
    linarith
  · -- case where x + 4 + 2 * sqrt 13 = 0 
    right
    linarith