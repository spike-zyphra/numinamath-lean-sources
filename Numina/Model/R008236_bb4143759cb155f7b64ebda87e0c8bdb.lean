import Mathlib

open Real Set
open scoped Real

theorem calculus_54903 :
  IsLeast {x | ∃ t : ℝ, x = (3 * sin t - 4 * cos t - 10) * (3 * sin t + 4 * cos t - 10)} 49 := by 
  constructor
  · use Real.pi / 2 
    have hsin : sin (Real.pi / 2) = 1 := by
      exact sin_pi_div_two
    have hcos : cos (Real.pi / 2) = 0 := by
      exact cos_pi_div_two
    rw [hsin, hcos]
    norm_num
  · intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : sin t ^ 2 + cos t ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq t
    have h2 : (3 * sin t - 4 * cos t - 10) * (3 * sin t + 4 * cos t - 10) ≥ 49 := by 
      nlinarith [sq_nonneg (sin t ^ 2 - 1), sq_nonneg (sin t ^ 2 - 4), sq_nonneg (sin t ^ 2 + cos t ^ 2 - 1), sq_nonneg (sin t), sq_nonneg (sin t - 1), sq_nonneg (sin t + 1), sq_nonneg (3 * sin t - 4 * cos t), sq_nonneg (4 * sin t + 3 * cos t), sq_nonneg (cos t), Real.sin_sq_add_cos_sq t, sq_nonneg (sin t - cos t), sq_nonneg (sin t + cos t)]
    linarith [ht, h2]