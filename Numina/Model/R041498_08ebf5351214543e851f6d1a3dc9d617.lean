import Mathlib

theorem algebra_233761 (v_e v_f : ℝ) (h_v : v_e > 0) (h_f : v_f > 0)
    (h_t : v_e / v_f = (v_e + v_f) / (v_e - v_f)) :
    v_e / v_f = 1 + Real.sqrt 2 := by

  have h1 : v_e - v_f ≠ 0 := by
    by_contra h
    have h_eq : v_e = v_f := by linarith
    rw [h_eq] at h_t
    field_simp [(show v_f ≠ 0 by linarith)] at h_t
    all_goals nlinarith

  have h2 : v_f ≠ 0 := by linarith

  field_simp [show v_f ≠ 0 by linarith, show v_e - v_f ≠ 0 by assumption] at h_t

  have h5 : (v_e) ^ 2 - 2 * (v_e) * (v_f) - (v_f) ^ 2 = 0 := by
    nlinarith

  have h6 : (v_e / v_f) ^ 2 - 2 * (v_e / v_f) - 1 = 0 := by
    have h5' : (v_e) ^ 2 - 2 * (v_e) * (v_f) - (v_f) ^ 2 = 0 := h5
    have h8 : v_f ≠ 0 := h2
    have eq2 : (v_e / v_f) ^ 2 - 2 * (v_e / v_f) - 1 = 0 := by
      field_simp [h8] at *
      nlinarith
    linarith

  have h7 : (v_e / v_f - (1 + Real.sqrt 2)) * (v_e / v_f - (1 - Real.sqrt 2)) = 0 := by
    nlinarith [h6, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt (2 : ℝ)), sq_nonneg (v_e / v_f), h_f, h_v]

  cases' (mul_eq_zero.mp h7) with h8 h9
  · -- case where v_e / v_f = 1 + sqrt 2
    linarith

  · -- case where v_e / v_f = 1 - sqrt 2
    have h6 : Real.sqrt 2 > 0 := by
      positivity

    have h7 : v_e / v_f < 0 := by
      nlinarith [h9, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]

    have h8 : v_e / v_f > 0 := by
      apply div_pos
      all_goals linarith

    linarith