import Mathlib

theorem algebra_297004 (f : ℝ → ℝ) (m a b : ℝ) (h₀ : ∀ x, f x = 2 * x + m)
    (h₁ : a = f 0) (h₂ : b = f m) (h₃ : b - a = m + 5) :
    m = 5 := by
  have ha : a = m := by
    rw [h₁, h₀ 0]
    all_goals linarith
  have hb : b = 3 * m := by 
    rw [h₂, h₀ m]
    all_goals ring
  rw [ha, hb] at h₃
  linarith