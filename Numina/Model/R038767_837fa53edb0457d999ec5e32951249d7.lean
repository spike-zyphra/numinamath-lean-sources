import Mathlib

open Real Set
open scoped Real

theorem algebra_6572 : IsGreatest (range (λ x => 2 * sin x ^ 2 + cos x + 1)) (3 + 1 / 8) := by
  constructor 
  · -- Show that 3 + 1/8 is in the range
    use Real.arccos (1 / 4)
    have h1 : cos (Real.arccos (1 / 4)) = 1 / 4 := by 
      apply Real.cos_arccos
      all_goals norm_num
    have h2 : sin (Real.arccos (1 / 4)) ^ 2 = 15 / 16 := by
      have h3 : sin (Real.arccos (1 / 4)) ^ 2 + cos (Real.arccos (1 / 4)) ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq (Real.arccos (1 / 4))
      rw [show cos (Real.arccos (1 / 4)) = 1 / 4 by linarith [h1]] at h3
      nlinarith 
    have eq1 : 2 * sin (Real.arccos (1 / 4)) ^ 2 + cos (Real.arccos (1 / 4)) + 1 = 3 + 1 / 8 := by
      rw [show sin (Real.arccos (1 / 4)) ^ 2 = 15 / 16 by linarith [h2]]
      rw [show cos (Real.arccos (1 / 4)) = 1 / 4 by linarith [h1]]
      norm_num 
    linarith [eq1]
  · -- Show that 3 + 1/8 is the greatest 
    intro y 
    rintro ⟨x, hx⟩ 
    simp at hx 
    have h21 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x 
    have h24 : 2 * sin x ^ 2 + cos x + 1 ≤ (3 + 1 / 8 : ℝ) := by 
      nlinarith [sq_nonneg (cos x - 1 / 4), sq_nonneg (sin x ^ 2 - 15 / 16), sq_nonneg (cos x - 1 / 4), sq_nonneg (cos x - 1), sq_nonneg (cos x + 1), sq_nonneg (sin x ^ 2 - 15 / 16), Real.sin_sq_add_cos_sq x]
    linarith [h24, show (3 + 1 / 8 : ℝ) = (25 / 8 : ℝ) by norm_num]