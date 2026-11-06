import Mathlib

theorem algebra_226761 {x : ℝ} (hx : x ≠ 0) (h : (1 / 6) * x * 1.2 + (1 / 2) * x * 0.9 + (1 / 3) * x * (1 + y / 100) = x) :
    y = 5 := by
  have eq2 : x * ( (1 / 6) * 1.2 + (1 / 2) * 0.9 + (1 / 3) * (1 + y / 100) - 1) = 0 := by
    linarith
  cases (mul_eq_zero.mp eq2) with
  | inl h3 =>
    exfalso
    exact hx h3
  | inr h4 =>
    ring_nf at h4
    linarith