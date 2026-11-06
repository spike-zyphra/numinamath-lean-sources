import Mathlib

theorem algebra_98449 (b a o : ℝ) (h₀ : 3 * b = 2 * a) (h₁ : 6 * a = 4 * o) :
18 * b = 8 * o := by
  -- Multiply both sides of the equation by 6 and 2, respectively.
  rw [← mul_right_inj' ((by simp):(6:ℝ)≠0),
      ← mul_assoc, ← mul_assoc] at h₀
  rw [← mul_right_inj' ((by simp):(2:ℝ)≠0),
      ← mul_assoc, ← mul_assoc] at h₁
  norm_num at h₀ h₁
  -- Carrying the first equation into the second
  rw [← h₀] at h₁
  -- We are able to get the final conclusion directly
  exact h₁