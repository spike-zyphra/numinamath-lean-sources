import Mathlib

theorem algebra_165511 (x : ℝ) (hx : (x + 1)^5 + (x - 1)^5 = 32 * x) :
    x = 0 ∨ x = -1 ∨ x = 1 := by
  have eq : (x + 1) ^ 5 + (x - 1) ^ 5 = 2 * x ^ 5 + 20 * x ^ 3 + 10 * x := by
    ring
  rw [eq] at hx
  have eq1 : 2 * x ^ 5 + 20 * x ^ 3 + 10 * x - 32 * x = 0 := by linarith
  have eq2 : 2 * x ^ 5 + 20 * x ^ 3 + 10 * x - 32 * x = x * (2 * x^4 + 20 * x^2 - 22) := by
    ring
  rw [eq2] at eq1
  have h : x * (2 * x^4 + 20 * x^2 - 22) = 0 := eq1
  cases' (mul_eq_zero.mp h) with hx1 hx2
  · -- Case $x = 0$
    left
    exact hx1
  · -- Case $2x^4 + 20x^2 - 22 = 0$
    have eq3 : 2 * x^4 + 20 * x^2 - 22 = 0 := by linarith
    have h2 : x^2 = 1 := by
      nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x^2 + 1)]
    have : x = 1 ∨ x = -1 := by
      rw [sq_eq_one_iff] at h2
      exact h2
    cases' this with h3 h4
    · -- Case x = 1
      right
      right
      exact h3
    · -- Case x = -1
      right
      left
      linarith