import Mathlib

theorem algebra_15358 {a b c : ℝ} (ha : a ≠ 0) (hvertex : ∀ x, a * x ^ 2 + b * x + c = a * (x + 4) ^ 2)
    (hpoint : a * 1 ^ 2 + b * 1 + c = -75) : a = -3 := by 
  have eq1 := hvertex 1
  have eq2 := hvertex 0
  have hc : c = 16 * a := by
    nlinarith
  nlinarith [hpoint, eq1, hc]