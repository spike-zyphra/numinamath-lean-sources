import Mathlib

theorem algebra_2588 (x y : ℝ) :
  -3 * x ^ 2 * y + 4 * x ^ 2 * y + 5 * x ^ 2 * y - 7 * x ^ 2 * y ^ 2 + abs (-8 * x ^ 2 * y ^ 2) =
  6 * x ^ 2 * y + x ^ 2 * y ^ 2 := by
    have h1 : abs (-8 * x ^ 2 * y ^ 2) = 8 * x ^ 2 * y ^ 2 := by
      have h2 : -8 * x ^ 2 * y ^ 2 ≤ 0 := by
        have h3 : x ^ 2 ≥ 0 := sq_nonneg x
        have h4 : y ^ 2 ≥ 0 := sq_nonneg y
        nlinarith [sq_nonneg (x * y)]
      rw [abs_of_nonpos h2]
      ring
      all_goals nlinarith [sq_nonneg (x * y)]
    rw [h1]
    ring