import Mathlib

theorem algebra_192643 {x : ℕ} (hx : x ≥ 20) (h : 30 * x / 100 = 20 * x / 100 + 5 * x / 100) :
    x ≤ 36 := by
  omega