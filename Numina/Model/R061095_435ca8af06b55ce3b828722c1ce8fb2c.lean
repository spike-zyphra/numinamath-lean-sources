import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_105549 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = sqrt (1 + sin x) + sqrt (1 - sin x)) :
  IsGreatest (range f) 2 := by
  constructor
  · -- First we shown that 2 is in the range of f
    use 0
    specialize h₀ 0
    rw [h₀]
    have h1 : sqrt (1 + sin (0 : ℝ)) = 1 := by
      simp [sin_zero]
      all_goals norm_num
    have h2 : sqrt (1 - sin (0 : ℝ)) = 1 := by
      simp [sin_zero]
      all_goals norm_num
    rw [h1, h2]
    all_goals norm_num
  · -- Then we need to show that for all x, f(x) ≤ 2
    intro y
    rintro ⟨x, hx⟩
    specialize h₀ x
    rw [h₀] at hx
    have h1 : sqrt (1 + sin x) ≥ 0 := Real.sqrt_nonneg (1 + sin x)
    have h2 : sqrt (1 - sin x) ≥ 0 := Real.sqrt_nonneg (1 - sin x)
    nlinarith [sq_nonneg (sqrt (1 + sin x) - 1), sq_nonneg (sqrt (1 - sin x) - 1),
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 + sin x by linarith [Real.neg_one_le_sin x, Real.sin_le_one x]), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 - sin x by linarith [Real.neg_one_le_sin x, Real.sin_le_one x]), 
      Real.cos_sq_add_sin_sq x]