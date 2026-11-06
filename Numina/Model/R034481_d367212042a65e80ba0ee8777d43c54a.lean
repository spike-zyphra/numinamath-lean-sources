import Mathlib

theorem algebra_66931 (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (h : y^3 = x^3 + 8 * x^2 - 6 * x + 8) :
    (x, y) = (9, 11) := by 
  have h1 : y > x := by
    nlinarith [sq_nonneg (y - x), sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (x - 9), sq_nonneg (y - 11)]
  have h2 : y ≤ x + 2 := by
    nlinarith [sq_nonneg (y - (x + 2)), sq_nonneg (x - 9), sq_nonneg (y - 11), sq_nonneg (x + 1), sq_nonneg (y + 1)]
  have h3 : y = x + 1 ∨ y = x + 2 := by
    omega
  rcases h3 with (h3 | h3)
  · -- Case where y = x + 1
    rw [show y = x + 1 by linarith] at h
    have h4 : 5 * x ^ 2 - 9 * x + 7 = 0 := by
      nlinarith
    have h5 : 5 * x ^ 2 - 9 * x + 7 > 0 := by
      nlinarith [sq_nonneg (x - 9 / 5 : ℤ)]
    nlinarith
  · -- Case where y = x + 2
    rw [show y = x + 2 by linarith] at h
    have h6 : 2 * x ^ 2 - 18 * x = 0 := by
      nlinarith
    have h7 : x * (x - 9) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h7) with h8 h9
    · -- Case x = 0
      nlinarith
    · -- Case x - 9 = 0
      have h8 : x = 9 := by linarith
      have h9 : y = 11 := by linarith [h3, h8]
      simp [h8, h9]
      <;> nlinarith