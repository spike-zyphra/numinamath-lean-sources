import Mathlib

theorem algebra_322142 {f : ℝ → ℝ} (hf : ∀ x, f (1 - x^2) = (1 - x^2) / x^2) :
    f (1 / 2) = 1 := by
  have h1 := hf (Real.sqrt (1 / 2))
  have h2 : (Real.sqrt (1 / 2) : ℝ) ^ 2 = (1 / 2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h3 : (1 - (Real.sqrt (1 / 2) : ℝ) ^ 2 : ℝ) = (1 / 2 : ℝ) := by 
    rw [h2]
    all_goals norm_num
  have h4 : f (1 - (Real.sqrt (1 / 2) : ℝ) ^ 2) = (1 - (Real.sqrt (1 / 2) : ℝ) ^ 2) / ((Real.sqrt (1 / 2) : ℝ) ^ 2) := by 
    simpa using h1
  rw [h3] at h4
  have h5 : (Real.sqrt (1 / 2) : ℝ) ^ 2 = (1 / 2 : ℝ) := h2
  rw [h5] at h4
  norm_num at h4 
  linarith