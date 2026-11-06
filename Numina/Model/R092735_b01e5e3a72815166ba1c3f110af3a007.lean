import Mathlib

theorem algebra_20314 (x : ℝ) : (x - 7) * (x - 3) * (x + 1) * (x + 5) = 1680 ↔
    x = 9 ∨ x = -7 := by
  constructor
  · -- Forward direction: If the equation holds, then x is either 9 or -7
    intro h
    have eq1 : (x - 7) * (x - 3) * (x + 1) * (x + 5) = (x^2 - 2*x - 35) * (x^2 - 2*x - 3) := by ring
    rw [eq1] at h
    have eq2 : (x^2 - 2*x - 35) * (x^2 - 2*x - 3) - 1680 = 0 := by linarith
    -- Substitute y = x^2 - 2*x, so (y - 35)(y - 3) = 1680
    have eq3 : (x^2 - 2 * x) ^ 2 - 38 * (x^2 - 2 * x) - 1575 = 0 := by
      nlinarith
    have eq4 : ((x^2 - 2 * x) - 63) * ((x^2 - 2 * x) + 25) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq4) with h5 h6
    · -- Case where (x^2 - 2*x - 63) = 0
      have eq5 : x^2 - 2 * x - 63 = 0 := by linarith
      have eq6 : (x - 9) * (x + 7) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp eq6) with h7 h8
      · -- Case where x - 9 = 0
        left
        linarith
      · -- Case where x + 7 = 0
        right
        linarith
    · -- Case where (x^2 - 2*x + 25) = 0
      have eq7 : x^2 - 2 * x + 25 = 0 := by nlinarith
      -- Show that the discriminant is negative
      have h9 : x ^ 2 - 2 * x + 25 > 0 := by 
        nlinarith [sq_nonneg (x - 1)]
      -- Contradiction, quadratic is positive, it can't be zero
      linarith
  · -- Backward direction
    rintro (h | h)
    · -- Case x = 9
      rw [h]
      norm_num
    · -- Case x = -7
      rw [h]
      norm_num