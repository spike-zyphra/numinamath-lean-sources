import Mathlib

theorem algebra_216228 {x k : ℝ} (hk : 0 ≤ k ∧ k ≤ 100) (hx : 0 ≤ x)
    (hA : 4 * 0.45 + x * k / 100 = (4 + x) * 0.5)
    (hB : 5 * 0.48 + (1 - x) * k / 100 = (5 + (1 - x)) * 0.5) :
    k = 80 := by
  linarith