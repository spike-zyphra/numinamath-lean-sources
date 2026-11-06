import Mathlib

theorem algebra_236496 (k p : ℕ) (h₀ : k = p + 5) (h₁ : k * (1 - 24 / 100 : ℝ) = p * (1 + 20 / 100 : ℝ) - 1) :
    k + p = 45 := by
  have h2 : (k : ℝ) = (p : ℝ) + 5 := by
    exact_mod_cast h₀
  rw [h2] at h₁
  -- Clear denominators
  norm_num at h₁
  have h3 : (p : ℝ) < 11 := by 
    nlinarith
  have h4 : p < 11 := by
    exact_mod_cast h3
  interval_cases p <;> norm_num at h₁ <;> omega