import Mathlib

theorem algebra_104385 {x y : ℝ} (hx : x^3-3*x^2+2000*x=1997) (hy : y^3-3*y^2+2000*y=1999) :
    x+y=2 := by
  -- Let's compute f(2 - x) manually and show it equals 1999 = f(y):
  have h2 : (2 - x) ^ 3 - 3 * (2 - x) ^ 2 + 2000 * (2 - x) = 1999 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (y - 1), sq_nonneg (y - 2),
          hx, hy, sq_nonneg (2 - x - y)]
  have h4 : y ^ 3 - 3 * y ^ 2 + 2000 * y = (2 - x) ^ 3 - 3 * (2 - x) ^ 2 + 2000 * (2 - x) := by 
    nlinarith [hx, hy, h2]
  have h5 : y = 2 - x := by 
    have h6 : (y - (2 - x)) * (y ^ 2 + y * (2 - x) + (2 - x) ^ 2 - 3 * (y + (2 - x)) + 2000) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · linarith
    · 
      -- When second factor is zero, derive contradiction
      have h8 : y ^ 2 + y * (2 - x) + (2 - x) ^ 2 - 3 * (y + (2 - x)) + 2000 = 0 := by
        linarith
      nlinarith [sq_nonneg (y - (2 - x)), sq_nonneg (y + (2 - x) - 1),
          sq_nonneg (x - 1), sq_nonneg (y - 1),
          sq_nonneg (x - y), sq_nonneg (2 - x - y)]
  linarith [h5]