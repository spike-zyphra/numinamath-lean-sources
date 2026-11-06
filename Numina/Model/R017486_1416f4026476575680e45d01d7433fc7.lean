import Mathlib

theorem algebra_164223 : Real.cos (Real.pi / 5) + Real.cos (2 * Real.pi / 5) +
    Real.cos (4 * Real.pi / 5) + Real.cos (6 * Real.pi / 5) = -1 / 2 := by
  have h1 : Real.cos (4 * Real.pi / 5) = - Real.cos (Real.pi / 5) := by
    have h2 : 4 * Real.pi / 5 = Real.pi - Real.pi / 5 := by ring
    rw [h2]
    rw [Real.cos_pi_sub]
  have h2 : Real.cos (6 * Real.pi / 5) = - Real.cos (Real.pi / 5) := by
    have h3 : 6 * Real.pi / 5 = Real.pi + Real.pi / 5 := by ring
    rw [h3]
    rw [Real.cos_add]
    simp [Real.cos_pi, Real.sin_pi]
  have h3 : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by 
    have h4 : Real.cos (2 * Real.pi / 5) = 2 * (Real.cos (Real.pi / 5)) ^ 2 - 1 := by
      have h5 : 2 * Real.pi / 5 = 2 * (Real.pi / 5) := by ring
      rw [h5]
      rw [Real.cos_two_mul]
    have h5 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
      exact Real.cos_pi_div_five
    rw [h4, h5]
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)]
  have h4 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
    exact Real.cos_pi_div_five
  rw [h1, h2, h3, h4]
  nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)]