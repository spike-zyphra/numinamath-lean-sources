import Mathlib

theorem algebra_95919 {f : ℝ → ℝ} (h : ∀ a b, f (a + b) + f (a - b) = 2 * f a * f b) : f 1 ≠ -2 := by 
  by_contra h1
  have h0 : f 0 = 1 := by
    have h10 := h 1 0
    norm_num at h10 
    rw [h1] at h10
    nlinarith 
  have h2 := h (1 / 2 : ℝ) (1 / 2 : ℝ)
  have eq1 : f ( (1 / 2 : ℝ) + (1 / 2 : ℝ) ) + f ( (1 / 2 : ℝ) - (1 / 2 : ℝ) ) = 2 * f (1 / 2 : ℝ) * f (1 / 2 : ℝ) := by
    simpa using h2 
  have eq2 : f ( (1 / 2 : ℝ) + (1 / 2 : ℝ) ) = f 1 := by 
    norm_num 
  have eq3 : f ( (1 / 2 : ℝ) - (1 / 2 : ℝ) ) = f 0 := by 
    norm_num 
  rw [eq2, eq3] at eq1 
  rw [h1, h0] at eq1 
  nlinarith [sq_nonneg (f (1 / 2 : ℝ) ) ]