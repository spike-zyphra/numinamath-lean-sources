import Mathlib
open Real Set

theorem algebra_8988 : IsGreatest {x | ∃ t : ℝ, x = sin (2 * t) + 2 * cos t - 3} (3 * √3 /2 - 3) := by 
  constructor 
  · -- Show 3 * √3 /2 - 3 can be attained.
    use (Real.pi / 6)
    have h1 : sin (2 * (Real.pi / 6)) = Real.sqrt 3 / 2 := by 
      have h2 : 2 * (Real.pi / 6) = Real.pi / 3 := by ring 
      rw [h2] 
      rw [sin_pi_div_three] 
    have h2 : cos (Real.pi / 6) = Real.sqrt 3 / 2 := by 
      rw [cos_pi_div_six] 
    rw [h1, h2] 
    linarith 
  · -- Show x ≤ 3 * √3 /2 - 3 for all x in the set
    intro x hx 
    rcases hx with ⟨t, ht⟩ 
    have h1 : sin (2 * t) = 2 * sin t * cos t := by 
      rw [sin_two_mul] 
    rw [h1] at ht 
    nlinarith [sq_nonneg (cos t - Real.sqrt 3 / 2), sq_nonneg (sin t - 1 / 2), 
        sq_nonneg (cos t + Real.sqrt 3 / 2), sq_nonneg (sin t + 1 / 2), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
        sq_nonneg (sin t ^ 2 + cos t ^ 2 - 1), 
        Real.sin_sq_add_cos_sq t
      ]