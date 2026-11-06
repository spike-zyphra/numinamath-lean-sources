import Mathlib

theorem algebra_315161 (x : ℝ) (hx : x ≠ 0 ∧ x ≠ 1) :
    (2 * x ^ 2 + 1) / (x ^ 2 * (x - 1) ^ 2) =
    2 / x + 1 / x ^ 2 + (-2) / (x - 1) + 3 / (x - 1) ^ 2 := by
  have hx1 : x ≠ 0 := hx.1
  have hx2 : x ≠ 1 := hx.2
  field_simp [(show x ≠ 0 by exact hx1),
             (show x - 1 ≠ 0 by intro h; apply hx2; linarith),
             (show x ^ 2 ≠ 0 by exact pow_ne_zero 2 hx1),
             (show (x - 1) ^ 2 ≠ 0 by exact pow_ne_zero 2 (show x - 1 ≠ 0 by intro h; apply hx2; linarith))]
  ring