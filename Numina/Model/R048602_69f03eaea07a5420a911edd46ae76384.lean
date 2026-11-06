import Mathlib

theorem algebra_97471 {f g : ℝ → ℝ} (hg : g = fun x => 1 - x ^ 2)
    (hf : ∀ x, x ≠ 0 → f (g x) = (1 - x ^ 2) / x ^ 2) :
    f (1 / 2) = 1 := by
  have h1 : g (Real.sqrt (1 / 2)) = 1 / 2 := by 
    rw [hg]
    have h2 : (Real.sqrt (1 / 2) : ℝ) ^ 2 = 1 / 2 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    simp [h2]
    all_goals norm_num
  
  have h3 : Real.sqrt (1 / 2) ≠ 0 := by 
    have h4 : 0 ≤ (Real.sqrt (1 / 2) : ℝ) := Real.sqrt_nonneg (1 / 2)
    have h5 : (Real.sqrt (1 / 2) : ℝ) > 0 := by
      have h6 : (1 / 2 : ℝ) > 0 := by norm_num
      have h7 : (Real.sqrt (1 / 2) : ℝ) > 0 := by
        apply Real.sqrt_pos.2 h6
      linarith [h7]
    linarith
  
  have h7 : f (g (Real.sqrt (1 / 2))) = (1 - (Real.sqrt (1 / 2)) ^ 2) / (Real.sqrt (1 / 2)) ^ 2 := hf (Real.sqrt (1 / 2)) h3
  
  rw [h1] at h7
  
  have h8 : (Real.sqrt (1 / 2) : ℝ) ^ 2 = 1 / 2 := by 
    rw [Real.sq_sqrt]
    all_goals norm_num
  
  rw [h8] at h7
  
  norm_num at h7
  
  linarith [h7]