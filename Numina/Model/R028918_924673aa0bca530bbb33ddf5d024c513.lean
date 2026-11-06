import Mathlib

open Real Set
open scoped Real 

theorem algebra_259028 {a : ℝ} (ha : a > sqrt 2) :
    IsLeast {x | ∃ t : ℝ, x = (sin t + a) * (cos t + a)} ((a - sqrt 2 / 2) ^ 2) := by
  constructor 
  · -- Show that (a - sqrt 2 / 2) ^ 2 is in the set 
    use 5 * (Real.pi) / 4
    have h11 : sin (5 * (Real.pi) / 4) = - (Real.sqrt 2 / 2) := by 
      have h13 : sin (5 * (Real.pi) / 4) = - sin (Real.pi / 4) := by 
        have h14 :  sin (5 * (Real.pi) / 4) = sin (Real.pi / 4 + Real.pi) := by 
          ring_nf 
        rw [h14] 
        rw [sin_add, sin_pi, cos_pi]
        all_goals ring_nf 
      have h14 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by 
        rw [sin_pi_div_four]
      rw [h13, h14]
    have h12 : cos (5 * (Real.pi) / 4) = - (Real.sqrt 2 / 2) := by 
      have h13 : cos (5 * (Real.pi) / 4) = - cos (Real.pi / 4) := by 
        have h14 :  cos (5 * (Real.pi) / 4) = cos (Real.pi / 4 + Real.pi) := by 
          ring_nf 
        rw [h14] 
        rw [cos_add, sin_pi, cos_pi]
        all_goals ring_nf 
      have h14 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by 
        rw [cos_pi_div_four]
      rw [h13, h14]
    rw [h11, h12]
    all_goals ring_nf 
  · -- Show that (a - sqrt 2 / 2) ^ 2 is the minimum
    intro x hx 
    rcases hx with ⟨t, ht⟩
    rw [ht]
    have h1 : sin t ^ 2 + cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
    have h3 : -Real.sqrt 2 ≤ sin t + cos t := by 
      nlinarith [sq_nonneg (sin t - cos t), sq_nonneg (sin t + cos t), Real.sqrt_nonneg 2, 
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sin_sq_add_cos_sq t, sq_nonneg (sin t ^ 2 - cos t ^ 2), sq_nonneg (sin t ^ 2 + cos t ^ 2 - 1)]
    have h4 : sin t + cos t ≤ Real.sqrt 2 := by 
      nlinarith [sq_nonneg (sin t - cos t), sq_nonneg (sin t + cos t), Real.sqrt_nonneg 2, 
        Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sin_sq_add_cos_sq t, sq_nonneg (sin t ^ 2 - cos t ^ 2), sq_nonneg (sin t ^ 2 + cos t ^ 2 - 1)]
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, 
      h3, h4, sq_nonneg (sin t + cos t + a), sq_nonneg ((sin t + cos t) + Real.sqrt 2), 
      sq_nonneg ((sin t - cos t)), sq_nonneg ((sin t + cos t) - a), mul_pos (show 0 < a - Real.sqrt 2 by linarith) (show 0 < a - Real.sqrt 2 by linarith), Real.sqrt_nonneg 2, 
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]