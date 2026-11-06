import Mathlib

theorem algebra_268831 (x y : ℤ) (hy : y = 1) (h : 4 * x - 2 * y + 3 = 3 * x + 3 * y) :
    x = 2 := by
  rw [hy] at h
  linarith