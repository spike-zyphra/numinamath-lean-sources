import Mathlib

theorem algebra_174929 (x y : ℤ) (hx : x > 0) (hy : y > 0)
    (h : 3 * x * y - 2 * x - y = 8) :
    (x = 9 ∧ y = 1) ∨ (x = 1 ∧ y = 5) := by
  have h1 : x ≤ 9 := by
    by_contra h1
    push_neg at h1
    have h3 : y < 1 := by
      nlinarith [sq_nonneg (x * y), sq_nonneg ((3 * x) - 1), sq_nonneg (y - 1), sq_nonneg (x - 9), sq_nonneg (y - 5)]
    have h4 : y ≤ 0 := by omega
    nlinarith
  interval_cases x <;> omega