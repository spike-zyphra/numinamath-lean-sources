import Mathlib

theorem number_theory_48562 (n : ℕ) (h : ∃ k : ℕ, Real.sqrt (1 + 12 * n ^ 2) = k) :
    IsSquare (2 + 2 * Real.sqrt (1 + 12 * n ^ 2)) := by
  rcases h with ⟨k, hk⟩
  have h1 : (k : ℝ) ^ 2 = 1 + 12 * (n : ℝ) ^ 2 := by
    have h2 : (Real.sqrt (1 + 12 * (n : ℝ) ^ 2)) ^ 2 = 1 + 12 * (n : ℝ) ^ 2 := by 
      rw [Real.sq_sqrt]
      all_goals norm_num
      all_goals nlinarith [sq_nonneg ((n : ℝ)), sq_nonneg ((k : ℝ)), sq_nonneg ((Real.sqrt (1 + 12 * (n : ℝ) ^ 2)) : ℝ)]
      all_goals positivity 
    have h3 : (k : ℝ) ^ 2 = (Real.sqrt (1 + 12 * (n : ℝ) ^ 2)) ^ 2 := by 
      rw [show (Real.sqrt (1 + 12 * (n : ℝ) ^ 2)) = (k : ℝ) by linarith [hk]]
      all_goals nlinarith 
      all_goals positivity 
    linarith [h2, h3]

  use Real.sqrt (2 + 2 * Real.sqrt (1 + 12 * n ^ 2))
  have h2 : Real.sqrt (2 + 2 * Real.sqrt (1 + 12 * n ^ 2)) ^ 2 = 2 + 2 * Real.sqrt (1 + 12 * n ^ 2) := by
    rw [Real.sq_sqrt]
    positivity 
  linarith [h2]