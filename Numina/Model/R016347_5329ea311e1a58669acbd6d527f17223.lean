import Mathlib

open Real Set
open scoped Real

theorem algebra_599243 :
  IsGreatest {y | ∃ x : ℝ, y = sin x ^ 2 + 2 * sin x * cos x + 3 * cos x ^ 2} (2 + sqrt 2) := by
  constructor
  · -- Show 2 + sqrt 2 is in the set
    use Real.pi / 8 
    have h1 : sin (Real.pi / 8) ^ 2 + 2 * sin (Real.pi / 8) * cos (Real.pi / 8) + 3 * cos (Real.pi / 8) ^ 2 = 2 + Real.sqrt 2 := by
      have h2 : sin (2 * (Real.pi / 8)) = 2 * sin (Real.pi / 8) * cos (Real.pi / 8) := by 
        rw [sin_two_mul]
      have h3 : cos (2 * (Real.pi / 8)) = 2 * cos (Real.pi / 8) ^ 2 - 1 := by 
        rw [cos_two_mul]
      have h4 : sin (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by 
        have h5 : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
        rw [h5]
        rw [sin_pi_div_four]
      have h5 : cos (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by 
        have h6 : 2 * (Real.pi / 8) = Real.pi / 4 := by ring 
        rw [h6]
        rw [cos_pi_div_four]
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 8), Real.sin_sq_add_cos_sq (2 * (Real.pi / 8)), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (sin (Real.pi / 8) ^ 2 - cos (Real.pi / 8) ^ 2), sq_nonneg (sin (Real.pi / 8) - cos (Real.pi / 8)), sq_nonneg (sin (Real.pi / 8) * cos (Real.pi / 8) - Real.sqrt 2 / 4)]
    linarith [h1]

  · -- Show that 2 + sqrt 2 is the greatest element in the set
    intro y hy
    rcases hy with ⟨x, hx⟩ 
    have h : sin x ^ 2 + 2 * sin x * cos x + 3 * cos x ^ 2 = 2 + sin (2 * x) + cos (2 * x) := by
      have h1 : sin x ^ 2 + 3 * cos x ^ 2 = 1 + 2 * cos x ^ 2 := by
        have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x 
        nlinarith 
      have h2 : sin (2 * x) = 2 * sin x * cos x := by 
        rw [sin_two_mul] 
      have h3 : cos (2 * x) = 2 * cos x ^ 2 - 1 := by 
        rw [cos_two_mul] 
      linarith [h1, h2, h3]
    rw [h] at hx 
    have h2 : sin (2 * x) + cos (2 * x) ≤ Real.sqrt 2 := by
      nlinarith [sq_nonneg (sin (2 * x) - cos (2 * x)), sq_nonneg (sin (2 * x) + cos (2 * x) - Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (sin (2 * x) + cos (2 * x)), Real.sin_sq_add_cos_sq (2 * x)]
    linarith [h2, hx]