import Mathlib

/- 7th Irish 1994 Problem B2 p, q, r are distinct reals such that q = p(4-p), r = q(4-q), p = r(4-r). Find all possible values of p+q+r. -/
theorem algebra_129322 {p q r : ℝ} (hqr : q = p * (4 - p)) (hrr : r = q * (4 - q))
    (hpp : p = r * (4 - r)) (hqr' : q ≠ r) (hpr : p ≠ r) (hqr'' : q ≠ p) :
    p + q + r = 6 ∨ p + q + r = 7 := by
  -- We'll prove that p+q+r equals either 6 or 7
  have h1 : (p + q + r) = 6 ∨ (p + q + r) = 7 := by
    -- First we'll show that (p+q+r)² - 13(p+q+r) + 42 = 0
    have h2 : (p + q + r) ^ 2 - 13 * (p + q + r) + 42 = 0 := by
      -- Using nonlinear arithmetic to prove this equation
      -- We use several facts:
      -- 1. The square of non-zero values is positive
      -- 2. The square of any real is non-negative
      -- 3. The given relations between p, q, and r
      nlinarith [sq_pos_of_ne_zero (show p - q ≠ 0 by intro h; apply hqr''; linarith),
        sq_pos_of_ne_zero (show p - r ≠ 0 by intro h; apply hpr; linarith),
        sq_pos_of_ne_zero (show q - r ≠ 0 by intro h; apply hqr'; linarith),
        sq_nonneg (p - q), sq_nonneg (p - r), sq_nonneg (q - r),
        hqr, hrr, hpp]
    -- Factoring the quadratic equation to (p+q+r-6)(p+q+r-7) = 0
    have h3 : (p + q + r - 6) * (p + q + r - 7) = 0 := by
      nlinarith [h2]
    -- Using the zero product property to conclude p+q+r equals either 6 or 7
    cases' (mul_eq_zero.mp h3) with h4 h5
    -- Case 1: p+q+r-6 = 0, so p+q+r = 6
    · left
      linarith
    -- Case 2: p+q+r-7 = 0, so p+q+r = 7
    · right
      linarith
  -- Conclude the proof by using our result
  exact h1
