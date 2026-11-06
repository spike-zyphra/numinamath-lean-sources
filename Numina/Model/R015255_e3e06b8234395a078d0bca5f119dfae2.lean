import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_144893 (x y : ℝ) (hx : 0 < y) (hy : y < x) (hxy : x * y = 1) :
    25 ≤ (3 * x ^ 3 + 125 * y ^ 3) / (x - y) := by
  have h1 : 0 < x := by
    nlinarith [hxy, hx]
  have h2 : 0 < x - y := by
    linarith
  have h3 : (3 * x ^ 3 + 125 * y ^ 3) / (x - y) ≥ 25 := by
    apply (le_div_iff₀ (by linarith)).mpr
    -- Now, we can write $25(x - y) \le 3x^3 +125y^3$
    have h4 : 3 * x ^ 3 + 125 * y ^ 3 -25 * (x - y) ≥ 0 := by
      have h5 : x * y = 1 := hxy
      -- Now, we have to show $3 * x ^ 3 + 125 * y ^ 3 -25 * x +25 * y \ge 0$
      -- multiply through by x to eliminate denominators (since $y=1/x$)
      -- This becomes $3 * x^4 + 125 / x -25x^2 -25/x \ge0$
      nlinarith [sq_nonneg (x -5 * y), sq_nonneg (x ^2 -5), sq_nonneg (y -1/5), sq_nonneg (y +1/5),
                  sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x^2 -25 * y^2),
                  mul_pos h1 hx, sq_nonneg (3 * x ^ 2 -25), sq_nonneg (5 * y -1), sq_nonneg (x -1)
                 ]
    linarith
  linarith [h3]