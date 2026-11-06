import Mathlib

theorem algebra_295816 (x y : ℤ) (hx : x ≥ 0) (hy : y ≥ 0)
    (h : (x - 1)^2 + (x + 1)^2 = y^2 + 1) :
    (3 * x + 2 * y, 4 * x + 3 * y) ∈ {(x, y) | (x - 1)^2 + (x + 1)^2 = y^2 + 1} := by 
  simp only [Set.mem_setOf_eq]
  nlinarith [h]