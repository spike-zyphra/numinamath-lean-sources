import Mathlib

theorem algebra_276020 {x y : ℝ} (hx : x ≠ 1) (hy : y^2 + 2 * y - 2 ≠ 0)
    (h : x / (x - 1) = (y^2 + 2 * y - 1) / (y^2 + 2 * y - 2)) :
    x = y^2 + 2 * y - 1 := by
  have h1 : x - 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have h2 : y^2 + 2 * y - 2 ≠ 0 := hy
  field_simp [(show x - 1 ≠ 0 by exact h1), (show y^2 + 2 * y - 2 ≠ 0 by exact h2)] at h ⊢ 
  linarith