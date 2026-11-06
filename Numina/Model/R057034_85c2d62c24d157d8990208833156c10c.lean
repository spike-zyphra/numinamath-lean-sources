import Mathlib

theorem algebra_2287 {a b c d : ℝ} (h₀ : a - b = 2) (h₁ : b - c = -3) (h₂ : c - d = 5) :
    (a - c) * (b - d) / (a - d) = -1 / 2 := by
  have had : a - d = 4 := by
    linarith
  have hac : a - c = -1 := by
    linarith
  have hbd : b - d = 2 := by
    linarith
  rw [hac, hbd, had]
  norm_num