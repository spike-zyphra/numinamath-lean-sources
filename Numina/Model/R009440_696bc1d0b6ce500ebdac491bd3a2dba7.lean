import Mathlib
theorem algebra_9030 (x : ℝ) (hx : x ^ 2 - 2 * x = 0) : x = 0 ∨ x = 2 := by
  have h : x * (x - 2) = 0 := by
    linarith [hx]

  cases' (mul_eq_zero.1 h) with h1 h2
  · -- x = 0
    left
    exact h1
  · -- x - 2 = 0, so x = 2
    right
    linarith