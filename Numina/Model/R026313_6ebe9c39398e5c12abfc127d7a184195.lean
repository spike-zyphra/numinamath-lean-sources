import Mathlib

theorem algebra_11250 {f : ℝ → ℝ} (hf : ∀ x, f x = Real.sin x + Real.sqrt 3 * Real.cos x + 1)
    (a b c : ℝ) (h : ∀ x, a * f x + b * f (x - c) = 1) :
    b * Real.cos c / a = -1 := by

  have eq1 := h 0
  rw [hf, hf] at eq1
  simp [Real.sin_zero, Real.cos_zero, Real.sin_neg, Real.cos_neg] at eq1

  have eq2 := h (Real.pi / 2)
  rw [hf, hf] at eq2
  simp [Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] at eq2

  have eq3 := h Real.pi
  rw [hf, hf] at eq3
  simp [Real.sin_pi, Real.cos_pi, Real.sin_pi_sub, Real.cos_pi_sub] at eq3

  have eq4 := h (Real.pi / 2 + c)
  rw [hf, hf] at eq4
  simp [Real.sin_add, Real.cos_add, Real.sin_pi_div_two, Real.cos_pi_div_two, mul_add] at eq4

  have ha1 : a ≠ 0 := by
    by_contra ha
    rw [ha] at eq1 eq2 eq3 eq4
    nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sin_sq_add_cos_sq c, sq_nonneg (Real.sin c ^ 2 - Real.cos c ^ 2)]

  have hb1 : b ≠ 0 := by
    by_contra hb
    rw [hb] at eq1 eq2 eq3 eq4
    nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sin_sq_add_cos_sq c, sq_nonneg (Real.sin c ^ 2 - Real.cos c ^ 2)]

  have h9 : b * Real.cos c / a = -1 := by
    have ha10 : a ≠ 0 := ha1
    field_simp [ha10]
    nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sin_sq_add_cos_sq c, sq_nonneg (Real.sin c ^ 2 - Real.cos c ^ 2)]
  exact h9