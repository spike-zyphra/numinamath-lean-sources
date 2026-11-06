import Mathlib

theorem algebra_12813 (a b c : ℝ) (h' : a > 0 ∧ b > 0 ∧ c > 0) (h₀ : (a + b + c) / 3 = 9)
    (h₁ : c - 4 = a) (h₂ : b + 3 = (2 / 3) * (a + 3)) :
    c = 13 := by
  have h3 : a + b + c = 27 := by
    linarith

  have h4 : c = a + 4 := by
    linarith

  have h5 : 2 * a - 3 * b = 3 := by
    linarith [h₂]

  have h6 : 2 * a + b = 23 := by 
    rw [h4] at h3
    linarith

  have h8 : a = 9 := by
    linarith [h6, h5]

  have h10 : c = 13 := by 
    rw [show a = 9 by linarith [h8]] at h4
    linarith [h4]

  exact h10