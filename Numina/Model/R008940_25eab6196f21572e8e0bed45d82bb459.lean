import Mathlib

theorem algebra_21278 (r y o w : ℕ) (h₀ : r + y + o + w = 35)
    (h₁ : (r : ℝ) / 2 = y - 2) (h₂ : (r : ℝ) / 2 = o / 3) (h₃ : (r : ℝ) / 2 = (w + 3 : ℝ) / 3) :
    r = 8 := by
  have h₀' : (r : ℝ) + (y : ℝ) + (o : ℝ) + (w : ℝ) = 35 := by
    exact_mod_cast h₀
  have eq1 : (y : ℝ) = (r : ℝ) / 2 + 2 := by linarith
  have eq2 : (o : ℝ) = 3 * (r : ℝ) / 2 := by linarith
  have eq3 : (w : ℝ) = 3 * (r : ℝ) / 2 - 3 := by linarith
  rw [eq1, eq2, eq3] at h₀'
  have hr : (r : ℝ) = 8 := by
    linarith
  have hr_nat : r = 8 := by
    exact_mod_cast hr
  exact hr_nat