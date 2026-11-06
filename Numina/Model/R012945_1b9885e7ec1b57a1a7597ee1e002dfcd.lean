import Mathlib

open Real

theorem algebra_163279 (α : ℝ) :
    2 * (cos (2 * α))^2 + 3 * cos (4 * α) - 3 =
    8 * cos (2 * α + π / 3) * cos (2 * α - π / 3) := by

  have h1 : cos (4 * α) = 2 * (cos (2 * α))^2 - 1 := by
    have h2 : cos (4 * α) = cos (2 * (2 * α)) := by ring_nf
    rw [h2]
    rw [cos_two_mul]
    all_goals ring_nf
  
  have eq1 : 2 * (cos (2 * α))^2 + 3 * cos (4 * α) - 3 = 8 * (cos (2 * α))^2 - 6 := by
    rw [h1]
    ring_nf

  have eq2 : 8 * cos (2 * α + π / 3) * cos (2 * α - π / 3) = 2 * (cos (2 * α))^2 - 6 * (sin (2 * α))^2 := by
    have h2 : cos (2 * α + π / 3) = cos (2 * α) * cos (π / 3) - sin (2 * α) * sin (π / 3) := by 
      rw [cos_add]
      all_goals ring_nf
    have h3 : cos (2 * α - π / 3) = cos (2 * α) * cos (π / 3) + sin (2 * α) * sin (π / 3) := by 
      rw [cos_sub]
      all_goals ring_nf
    rw [h2, h3]
    have h4 : cos (π / 3) = 1 / 2 := by 
      exact cos_pi_div_three
    have h5 : sin (π / 3) = Real.sqrt 3 / 2 := by 
      rw [sin_pi_div_three]
    rw [h4, h5]
    have h7 : 8 * (cos (2 * α) * (1 / 2) - sin (2 * α) * (Real.sqrt 3 / 2)) * (cos (2 * α) * (1 / 2) + sin (2 * α) * (Real.sqrt 3 / 2)) =
      2 * (cos (2 * α))^2 - 6 * (sin (2 * α))^2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_nonneg 3]
    linarith [h7]

  have eq3 : 2 * (cos (2 * α))^2 - 6 * (sin (2 * α))^2 = 8 * (cos (2 * α))^2 - 6 := by
    have h8 : (sin (2 * α))^2 = 1 - (cos (2 * α))^2 := by
      have h9 : (sin (2 * α))^2 + (cos (2 * α))^2 = 1 := by
        exact Real.sin_sq_add_cos_sq (2 * α)
      nlinarith
    rw [h8]
    ring_nf
    <;> linarith [Real.sin_sq_add_cos_sq (2 * α)]
  
  rw [eq1, eq2, eq3]
  all_goals linarith [Real.sin_sq_add_cos_sq (2 * α)]