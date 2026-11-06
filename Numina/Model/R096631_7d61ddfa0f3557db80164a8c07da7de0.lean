import Mathlib

theorem algebra_183657 {a b c : ℝ} (h : a + b * c = (a + b) * (a + c)) :
    a = 0 ∨ a + b + c = 1 := by
  have h1 : a = a ^ 2 + a * c + a * b := by
    have eq1 : (a + b) * (a + c) = a ^ 2 + a * c + a * b + b * c := by
      ring
    rw [eq1] at h
    linarith

  have h2 : a * (1 - a - b - c) = 0 := by
    linarith
  
  cases' (mul_eq_zero.1 h2) with h3 h4
  · -- Case where a = 0
    left
    exact h3
  · -- Case where 1 - a - b - c = 0, which implies a + b + c = 1
    right
    linarith