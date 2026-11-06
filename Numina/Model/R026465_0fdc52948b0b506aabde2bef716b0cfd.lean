import Mathlib

theorem algebra_10300 (x y : ℝ) (h₀ : Real.sin x + Real.sin y = (Real.sqrt 3 - 1) / 2)
    (h₁ : Real.cos x + Real.cos y = (Real.sqrt 3 + 1) / 2) :
    Real.cos (x + y) = Real.sqrt 3 / 2 := by
  have h2 : Real.cos (x + y) = Real.cos x * Real.cos y - Real.sin x * Real.sin y := by
    rw [Real.cos_add]
  -- Now need to prove `Real.cos (x + y) = Real.sqrt 3 / 2`.
  have eq1 : (Real.sin x + Real.sin y) ^ 2 + (Real.cos x + Real.cos y) ^ 2 = 2 := by 
    rw [h₀, h₁]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have eq2 : (Real.sin x + Real.sin y) * (Real.cos x + Real.cos y) = 1 / 2 := by 
    rw [h₀, h₁]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have eq3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have eq4 : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
  -- Now need to prove `h3 : Real.cos x * Real.cos y - Real.sin x * Real.sin y = Real.sqrt 3 / 2`
  have h3 : Real.cos x * Real.cos y - Real.sin x * Real.sin y = Real.sqrt 3 / 2 := by 
    have eq5 : Real.sin x * Real.sin y + Real.cos x * Real.cos y = 0 := by 
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num) ]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]
  rw [h2]
  linarith [h3]