import Mathlib

theorem algebra_254078 {x : ℝ} (hx : x > 0) :
    2.50 * x - 500.00 - 2.00 * x ≥ 0 ↔ x ≥ 1000 := by
  constructor
  · -- Forward direction: If 2.50 * x - 500.00 - 2.00 * x ≥ 0, then x ≥ 1000
    intro h
    norm_num at h ⊢
    linarith
  · -- Backward direction: If x ≥ 1000, then 2.50 * x - 500.00 - 2.00 * x ≥ 0
    intro h
    norm_num at h ⊢
    linarith