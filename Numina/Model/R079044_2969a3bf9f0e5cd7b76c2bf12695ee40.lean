import Mathlib

theorem algebra_181425 (x : Fin 42 → ℝ) (h : ∀ i, x i = 2 ∨ x i = 3)
    (h' : ∑ i, x i < 3 * 42) :
    ∑ i, x i ≤ 4 * 42 := by 
  linarith