import Mathlib

theorem algebra_163175 (α : ℝ) :
    (1 / Real.sqrt 3) * Real.sin (4 * α) + 1 - 2 * (Real.cos (2 * α))^2 =
    (2 / Real.sqrt 3) * Real.sin (4 * α - Real.pi / 3) := by
  have h1 : (1 / Real.sqrt 3) * Real.sin (4 * α) + 1 - 2 * (Real.cos (2 * α))^2 =
    (1 / Real.sqrt 3) * Real.sin (4 * α) - Real.cos (4 * α) := by
    have h2 : Real.cos (4 * α) = 2 * (Real.cos (2 * α)) ^ 2 - 1 := by
      have h3 : Real.cos (4 * α) = Real.cos (2 * (2 * α)) := by ring_nf
      rw [h3]
      rw [Real.cos_two_mul]
    linarith [h2]
  rw [h1]
  have h3 : Real.sin (4 * α - Real.pi / 3) = Real.sin (4 * α) * Real.cos (Real.pi / 3) - Real.cos (4 * α) * Real.sin (Real.pi / 3) := by 
    rw [Real.sin_sub]
  rw [h3]
  have h4 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three 
  have h5 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  rw [h4, h5]
  field_simp [show Real.sqrt 3 > 0 by positivity] 
  <;> ring_nf <;> field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  <;> ring