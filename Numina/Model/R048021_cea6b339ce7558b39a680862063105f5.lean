import Mathlib

open Real Set
open scoped Real

theorem algebra_9026 : IsLeast {x | ∃ t, x = sin t * cos t} (-1/2) := by
  constructor
  · -- First, let's prove that -1/2 is in the set.
    use -(Real.pi / 4)
    have h1 : sin (-(Real.pi / 4)) = -sin (Real.pi / 4) := by
      rw [sin_neg]
    have h2 : cos (-(Real.pi / 4)) = cos (Real.pi / 4) := by 
      rw [cos_neg]
    rw [h1, h2]
    have h3 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      exact sin_pi_div_four
    have h4 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      exact cos_pi_div_four
    rw [h3, h4]
    have h5 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
      exact Real.sq_sqrt (by norm_num)
    nlinarith [h5]
  · -- Now, let's prove that -1/2 is the least element in the set
    intro x hx 
    rcases hx with ⟨t, ht⟩ 
    have h6 : sin t * cos t ≥ -1 / 2 := by
      have h1 : sin t ^ 2 + cos t ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq t 
      nlinarith [sq_nonneg (sin t + cos t), sq_nonneg (sin t - cos t), Real.sin_sq_add_cos_sq t]
    linarith [h6, ht]