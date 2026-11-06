import Mathlib

open Real

theorem inequalities_266781 (t : ℝ) (ht : t > 0) :
    0 ≤ (t ^ 2 + 1) / (t + 1) - sqrt t ∧ (t ^ 2 + 1) / (t + 1) - sqrt t ≤ |t - 1| := by
  have ht1 : t + 1 > 0 := by linarith
  have h1 : sqrt t ≥ 0 := by positivity
  have h2 : (sqrt t) ^ 2 = t := sq_sqrt (by linarith)
  constructor
  · -- Prove that 0 ≤ (t ^ 2 + 1) / (t + 1) - sqrt t
    have h3 : (t ^ 2 + 1 : ℝ) / (t + 1) ≥ sqrt t := by
      have h4 : (t ^ 2 + 1 : ℝ) ≥ (sqrt t : ℝ) * (t + 1) := by
        nlinarith [sq_nonneg (t - 1), sq_nonneg (sqrt t - 1), h2, sq_nonneg (t ^ 2 - t), sq_nonneg ((sqrt t) ^ 2 - t), 
          mul_pos ht (show (0 : ℝ) < t + 1 by linarith), Real.sqrt_nonneg t, 
          sq_nonneg (t ^ 2 - t + 1), sq_nonneg (t - (sqrt t) ^ 2)]
      have h5 : (t ^ 2 + 1 : ℝ) / (t + 1) ≥ (sqrt t : ℝ) := by
        have pos1 : t + 1 > 0 := ht1
        apply (le_div_iff₀ pos1).mpr
        linarith
      exact h5
    linarith
  · -- Prove that (t ^ 2 + 1) / (t + 1) - sqrt t ≤ |t - 1|
    by_cases h : t ≥ 1
    · -- t ≥ 1
      rw [abs_of_nonneg (by linarith)]
      have h6 : (t ^ 2 + 1 : ℝ) / (t + 1) - sqrt t ≤ t - 1 := by
        have h7 : (t ^ 2 + 1 : ℝ) / (t + 1) ≤ sqrt t + (t - 1 : ℝ) := by
          have h8 : (t ^ 2 + 1 : ℝ) ≤ (sqrt t + (t - 1 : ℝ)) * (t + 1 : ℝ) := by
            nlinarith [sq_nonneg (t - 1), sq_nonneg (sqrt t - 1), h2, sq_nonneg (t ^ 2 - t), sq_nonneg ((sqrt t) ^ 2 - t), 
              mul_pos ht (show (0 : ℝ) < t + 1 by linarith), Real.sqrt_nonneg t, 
              sq_nonneg (t ^ 2 - t + 1), sq_nonneg (t - (sqrt t) ^ 2)]
          have ht2 : t + 1 > 0 := ht1
          apply (div_le_iff₀ ht2).mpr
          linarith
        linarith
      linarith
    · -- t < 1
      rw [abs_of_neg (by linarith)]
      have h7 : (t ^ 2 + 1 : ℝ) / (t + 1) - sqrt t ≤ (1 - t : ℝ) := by
        have h8 : (t ^ 2 + 1 : ℝ) / (t + 1) ≤ sqrt t + (1 - t : ℝ) := by
          have h9 : (t ^ 2 + 1 : ℝ) ≤ (sqrt t + (1 - t : ℝ)) * (t + 1 : ℝ) := by
            nlinarith [sq_nonneg (t - 1), sq_nonneg (sqrt t - 1), h2, sq_nonneg (t ^ 2 - t), sq_nonneg ((sqrt t) ^ 2 - t), 
              mul_pos ht (show (0 : ℝ) < t + 1 by linarith), Real.sqrt_nonneg t, 
              sq_nonneg (t ^ 2 - t + 1), sq_nonneg (t - (sqrt t) ^ 2)]
          have ht2 : t + 1 > 0 := ht1
          apply (div_le_iff₀ ht2).mpr
          linarith
        linarith
      linarith