import Mathlib

theorem number_theory_2420 {n : ℕ} {a : ℝ} (ha : a > 1) (h : √n = a) :
    √(n - 1) = Real.sqrt (a ^ 2 - 1) ∧ √(n + 1) = Real.sqrt (a ^ 2 + 1) := by
  have h1 : (n : ℝ) = a ^ 2 := by 
    calc 
      (n : ℝ) = (√n) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = a ^ 2 := by rw [h]

  have h2 : √(n - 1) = Real.sqrt (a ^ 2 - 1) := by
    have h3 : (n - 1 : ℝ) = (a ^ 2 - 1 : ℝ) := by
      have h3 : (n : ℝ) = a ^ 2 := h1 
      linarith
    rw [show (n - 1 : ℝ) = (a ^ 2 - 1 : ℝ) by linarith [h3]]
    all_goals norm_num
  
  have h4 : √(n + 1) = Real.sqrt (a ^ 2 + 1) := by
    have h5 : (n + 1 : ℝ) = (a ^ 2 + 1 : ℝ) := by 
      have h5 : (n : ℝ) = a ^ 2 := h1 
      linarith 
    rw [show (n + 1 : ℝ) = (a ^ 2 + 1 : ℝ) by linarith [h5]]
    all_goals norm_num
  
  exact ⟨h2, h4⟩