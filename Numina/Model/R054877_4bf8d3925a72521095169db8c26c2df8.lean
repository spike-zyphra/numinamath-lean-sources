import Mathlib

theorem algebra_139622 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * 0.8) / (y * 1.28) = (x / y) * (1 - 37.5 / 100) := by
  field_simp [hy, hx]
  ring_nf