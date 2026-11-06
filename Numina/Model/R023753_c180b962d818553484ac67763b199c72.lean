import Mathlib

theorem algebra_6025 (α : ℝ) :
    1 - Real.sin α - Real.cos α = 2 * Real.sqrt 2 * Real.sin (α / 2) * Real.sin (α / 2 - Real.pi / 4) := by
  have h1 : Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by
    rw [←Real.sin_two_mul]
    ring_nf
  have h2 : Real.cos α = 1 - 2 * Real.sin (α / 2) ^ 2 := by
    have hcos : Real.cos α = 2 * Real.cos (α / 2) ^ 2 - 1 := by 
      rw [←Real.cos_two_mul]
      ring_nf
    have hcos2 : Real.cos (α / 2) ^ 2 = 1 - Real.sin (α / 2) ^ 2 := by
      rw [← Real.sin_sq_add_cos_sq (α / 2)]
      linarith
    rw [hcos2] at hcos
    nlinarith 
  have h3 : Real.sin (α / 2 - Real.pi / 4) = ( (Real.sin (α / 2) - Real.cos (α / 2)) * Real.sqrt 2 / 2 ) := by
    rw [Real.sin_sub]
    have hsin : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    have hcos : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    rw [hsin, hcos]
    all_goals 
      ring
  rw [h1, h2, h3]
  have h4 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h5 : Real.sin (α / 2) ^ 2 + Real.cos (α / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (α / 2)
  -- evaluate both side after expansion
  -- left side simplified to 2 sin^2(x/2) - 2 sin(x/2) cos(x/2)
  -- right side simplified to the same result
  ring_nf 
  <;> 
    simp [Real.sqrt_mul_self, h4, Real.sin_sq, Real.cos_sq] at *
  <;> 
    nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num : (0:ℝ) < 2), Real.sqrt_nonneg 2, sq_nonneg (Real.sin (α / 2) - Real.cos (α / 2)), sq_nonneg (Real.sin (α / 2) ^ 2 - Real.cos (α / 2) ^ 2), Real.sin_sq_add_cos_sq (α / 2)]