import Mathlib

open Real Set
open scoped Real

theorem algebra_185642 (α : ℝ) :
  cos (π/6 - α/2) * sin (π/3 - α/2) * sin (α/2) = sin (3*α/2)/4 := by
  have h1 : cos (π / 6 - α / 2) = cos (π / 6) * cos (α / 2) + sin (π / 6) * sin (α / 2) := by 
    rw [cos_sub]
  have h2 : sin (π / 3 - α / 2) = sin (π / 3) * cos (α / 2) - cos (π / 3) * sin (α / 2) := by 
    rw [sin_sub]
  have h3 : cos (π / 6) = Real.sqrt 3 / 2 := by 
    rw [cos_pi_div_six]
  have h4 : sin (π / 6) = 1 / 2 := by 
    rw [sin_pi_div_six]
  have h5 : sin (π / 3) = Real.sqrt 3 / 2 := by 
    rw [sin_pi_div_three]
  have h6 : cos (π / 3) = 1 / 2 := by 
    rw [cos_pi_div_three]
  rw [h1, h2, h3, h4, h5, h6]
  have h8 : sin (3 * α / 2) = 3 * sin (α / 2) - 4 * sin (α / 2) ^ 3 := by 
    have h9 : 3 * α / 2 = 3 * (α / 2) := by 
      ring
    rw [h9]
    rw [sin_three_mul]
  have eq1 : (Real.sqrt 3 / 2 * cos (α / 2) + 1 / 2 * sin (α / 2)) * (Real.sqrt 3 / 2 * cos (α / 2) - 1 / 2 * sin (α / 2)) = (3 / 4) * cos (α / 2) ^ 2 - (1 / 4) * sin (α / 2) ^ 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by linarith : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by linarith : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_nonneg 3, sq_nonneg (cos (α / 2) ^ 2 - sin (α / 2) ^ 2), sq_nonneg (sin (α / 2) * cos (α / 2)), sq_nonneg (Real.sqrt 3), Real.sin_sq_add_cos_sq (α / 2)]
  have eq2 : ( (3 / 4) * cos (α / 2) ^ 2 - (1 / 4) * sin (α / 2) ^ 2 ) * sin (α / 2) = (3 / 4) * cos (α / 2) ^ 2 * sin (α / 2) - (1 / 4) * sin (α / 2) ^ 3 := by ring
  calc 
    ((Real.sqrt 3 / 2 * cos (α / 2) + 1 / 2 * sin (α / 2)) * (Real.sqrt 3 / 2 * cos (α / 2) - 1 / 2 * sin (α / 2)) ) * sin (α / 2)
        = ((3 / 4) * cos (α / 2) ^ 2 - (1 / 4) * sin (α / 2) ^ 2) * sin (α / 2) := by
          rw [eq1]
    _ = (3 / 4) * cos (α / 2) ^ 2 * sin (α / 2) - (1 / 4) * sin (α / 2) ^ 3 := by 
      rw [eq2]
    _ = (1 / 4) * (3 * cos (α / 2) ^ 2 * sin (α / 2) - sin (α / 2) ^ 3) := by ring
    _ = (1 / 4) * (3 * sin (α / 2) - 4 * sin (α / 2) ^ 3) := by
      have h9 : 3 * cos (α / 2) ^ 2 * sin (α / 2) - sin (α / 2) ^ 3 = 3 * sin (α / 2) - 4 * sin (α / 2) ^ 3 := by
        have hcos : cos (α / 2) ^ 2 = 1 - sin (α / 2) ^ 2 := by 
          have h : sin (α / 2) ^ 2 + cos (α / 2) ^ 2 = 1 := by 
            exact Real.sin_sq_add_cos_sq (α / 2)
          linarith
        rw [hcos]
        ring
      rw [h9]
    _ = (1 / 4) * sin (3 * α / 2) := by 
      rw [h8]
    _ = sin (3 * α / 2) / 4 := by ring