import Mathlib

open Real Set

theorem algebra_314992 :
    IsGreatest {x | ∃ a b : ℝ, x = (2 * a + sqrt 2 * b) / (2 * a ^ 4 + 4 * b ^ 4 + 9)} (1 / 4) := by
  constructor 
  · -- Show 1/4 is achievable by finding specific a, b
    use 1, Real.sqrt 2 / 2
    have h2 : (2 * (1 : ℝ) + Real.sqrt 2 * (Real.sqrt 2 / 2)) = 3 := by 
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h3 : (2 * (1 : ℝ) ^ 4 + 4 * (Real.sqrt 2 / 2) ^ 4 + 9) = 12 := by 
      have h1 : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by 
        nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h2 : (Real.sqrt 2 / 2) ^ 4 = (1 / 4 : ℝ) := by 
        calc 
          (Real.sqrt 2 / 2) ^ 4 = ((Real.sqrt 2 / 2) ^ 2) ^ 2 := by ring 
          _ = (1 / 2) ^ 2 := by rw [h1]
          _ = (1 / 4 : ℝ) := by norm_num
      nlinarith [h2, Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]
    rw [h2, h3]
    norm_num 
  · -- Show 1/4 is the greatest such value
    intro x hx 
    rcases hx with ⟨ a, b, hx_eq ⟩
    have h1 : (2 * a + Real.sqrt 2 * b) / (2 * a ^ 4 + 4 * b ^ 4 + 9) ≤ (1 / 4 : ℝ) := by 
      have hdenom_pos : (2 * a ^ 4 + 4 * b ^ 4 + 9) > 0 := by positivity 
      have h2 : 2 * a + Real.sqrt 2 * b ≤ (1 / 4 : ℝ) * (2 * a ^ 4 + 4 * b ^ 4 + 9) := by 
        nlinarith [sq_nonneg (a ^ 2 - 2), sq_nonneg (a - 1), sq_nonneg (b - Real.sqrt 2 / 2), sq_nonneg (a ^ 2 - 2 * a), 
          sq_nonneg (b ^ 2 - 1 / 2), 
          sq_nonneg (a * (Real.sqrt 2 / 2) - b ), 
          sq_nonneg (a - Real.sqrt 2 / 2), 
          Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), 
          sq_nonneg ( (2 * a - Real.sqrt 2 * b) - (2 * (Real.sqrt 2 / 2)) ), 
          sq_nonneg ( a * Real.sqrt 2 - b * 2 ) ]
      apply (div_le_iff₀ hdenom_pos).mpr 
      linarith [h2] 
    linarith [hx_eq, h1]