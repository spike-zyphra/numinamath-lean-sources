import Mathlib

theorem algebra_12671 (A B C D : ℝ) (h₀ : A < B) (h₁ : B < C) (h₂ : C < D)
    (h₃ : B - A = 2) (h₄ : C - B = 5) (h₅ : D - A = 14) :
    (C - A) / (D - B) = 7 / 12 := by
  have h₆ : C - A = 7 := by
    linarith
  have h₇ : D - B = 12 := by
    linarith
  rw [h₆, h₇]
  all_goals linarith