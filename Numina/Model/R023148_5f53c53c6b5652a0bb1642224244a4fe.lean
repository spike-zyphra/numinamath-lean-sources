import Mathlib

open Real

theorem calculus_22864 : tan (π / 8) = sqrt 2 - 1 := by
  have h1 : tan (π / 4) = 1 := by
    rw [tan_pi_div_four]
  have h2 : tan (π / 4) = 2 * tan (π / 8) / (1 - tan (π / 8) ^ 2) := by
    rw [show π / 4 = 2 * (π / 8) by ring]
    rw [tan_two_mul]
  rw [h1] at h2
  have h3 : 1 - tan (π / 8) ^ 2 ≠ 0 := by
    by_contra h
    have h4 : tan (π / 8) ^ 2 = 1 := by linarith
    have h5 : tan (π / 8) > 0 := by
      apply tan_pos_of_pos_of_lt_pi_div_two
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have h6 : tan (π / 8) = 1 := by
      nlinarith [h4, h5]
    rw [h6] at h2
    norm_num at h2
  have h4 : (1 - tan (π / 8) ^ 2) * 1 = 2 * tan (π / 8) := by
    field_simp [h3] at h2 ⊢
    nlinarith
  have h5 : tan (π / 8) ^ 2 + 2 * tan (π / 8) - 1 = 0 := by
    nlinarith [h4]
  have h6 : tan (π / 8) > 0 := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h7 : tan (π / 8) = Real.sqrt 2 - 1 := by
    have h8 : tan (π / 8) ^ 2 + 2 * tan (π / 8) - 1 = 0 := h5
    have h9 : tan (π / 8) ^ 2 + 2 * tan (π / 8) - 1 = (tan (π / 8) - (Real.sqrt 2 - 1)) * (tan (π / 8) - (-(Real.sqrt 2) - 1)) := by
      ring_nf
      rw [Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 2]
    rw [h9] at h8
    cases' (mul_eq_zero.mp h8) with h10 h11
    · -- tan (π / 8) = Real.sqrt 2 - 1
      linarith
    · -- tan (π / 8) = -Real.sqrt 2 - 1
      have h12 : tan (π / 8) = -Real.sqrt 2 - 1 := by linarith
      have h13 : tan (π / 8) < 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      linarith [h13, h6]
  linarith