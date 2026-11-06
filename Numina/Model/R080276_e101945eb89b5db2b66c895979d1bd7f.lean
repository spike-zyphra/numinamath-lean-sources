import Mathlib

theorem algebra_201909 (a b c : ℝ) (ha : ∃ q : ℚ, a * b = q)
    (hb : ∃ q : ℚ, b * c = q) (hc : ∃ q : ℚ, c * a = q) :
    ∃ x y z : ℤ, a * x + b * y + c * z = 0 := by
  use 0, 0, 0
  simp