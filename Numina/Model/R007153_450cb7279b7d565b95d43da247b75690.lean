import Mathlib

theorem algebra_17251 (A B C : ℝ × ℝ) (h₀ : A.1 + B.1 + C.1 = 10) :
    (A.1 + B.1) / 2 + (B.1 + C.1) / 2 + (C.1 + A.1) / 2 = 10 := by
  have eq1 : (A.1 + B.1) / 2 + (B.1 + C.1) / 2 + (C.1 + A.1) / 2 = (A.1 + B.1 + C.1) := by
    ring
  rw [eq1]
  exact h₀