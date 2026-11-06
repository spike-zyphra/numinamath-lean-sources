import Mathlib

theorem algebra_22209 (x : ℤ) (hx : x > 0) : 4 * x ^ 3 - 41 * x ^ 2 + 10 * x = 1989 ↔ x = 13 := by
  constructor
  · -- Forward direction: Assume 4 * x ^ 3 - 41 * x ^ 2 + 10 * x = 1989, show x = 13
    intro h
    have h1 : 4 * x ^ 3 - 41 * x ^ 2 + 10 * x - 1989 = 0 := by
      linarith
    have h2 : (x - 13) * (4 * x^2 + 11 * x + 153) = 0 := by
      ring_nf at h1 ⊢
      linarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case 1: h3 : x -13 = 0
      linarith
    · -- Case 2: h4 : 4 * x^2 + 11 * x + 153 = 0
      have h5 : x > 0 := hx
      have h6 : 4 * x ^ 2 + 11 * x + 153 > 0 := by
        nlinarith [sq_nonneg (x), h5]
      linarith
  · -- Backward direction: Assume x = 13, show 4 * x ^ 3 - 41 * x ^ 2 + 10 * x = 1989
    intro h
    rw [h]
    norm_num