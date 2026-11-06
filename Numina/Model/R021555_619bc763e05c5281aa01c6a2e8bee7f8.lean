import Mathlib

theorem algebra_164482 : Real.cos (3 * Real.pi / 5) * Real.cos (6 * Real.pi / 5) = 1 / 4 := by
  have h1 : Real.cos (6 * Real.pi / 5) = - Real.cos (Real.pi / 5) := by
    have h2 : 6 * Real.pi / 5 = Real.pi + Real.pi / 5 := by
      ring_nf
    rw [h2]
    rw [Real.cos_add]
    simp [Real.cos_pi, Real.sin_pi]

  have h3 : Real.cos (3 * Real.pi / 5) = - Real.cos (2 * Real.pi / 5) := by
    have h4 : 3 * Real.pi / 5 = Real.pi - 2 * Real.pi / 5 := by
      ring_nf
    rw [h4]
    rw [Real.cos_sub]
    simp [Real.cos_pi, Real.sin_pi]

  have h5 : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
    have h1 : Real.cos (2 * Real.pi / 5) = 2 * (Real.cos (Real.pi / 5) ) ^ 2 - 1 := by
      have h : 2 * Real.pi / 5 = 2 * (Real.pi / 5) := by ring
      rw [h]
      rw [Real.cos_two_mul]
    rw [h1]

    have h2 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
      have h3 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
        rw [Real.cos_pi_div_five]
      linarith
    rw [h2]
    field_simp
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]

  have h2 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
    have h3 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
      rw [Real.cos_pi_div_five]
    linarith

  rw [h1, h3, h5, h2]

  have h6 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show 0 ≤ 5 by norm_num)
  field_simp [h6]
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]