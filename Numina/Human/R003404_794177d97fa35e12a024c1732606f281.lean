import Mathlib

/- 2. (17 points) Find the largest root of the equation


$$

\left|\cos (\pi x)+x^{3}-3 x^{2}+3 x\right|=3-x^{2}-2 x^{3}

$$
 -/
theorem algebra_176943 :
    IsGreatest ({x | abs (Real.cos (Real.pi * x) + x ^ 3 - 3 * x ^ 2 + 3 * x) = 3 - x ^ 2 - 2 * x ^ 3}) 1
  := by
    -- consider the definition of "greatest number of set" and "upper bounds"
    unfold IsGreatest upperBounds

    -- prove both parts separately
    split_ands
    -- 1 is a root of the equation
    · norm_num
    -- we'll prove that every root is at most 1
    · norm_num
      intro x h

      -- assume the opposite, that x is larger than 1
      by_contra
      have lt_x : 1 < x := by linarith

      -- but then the LHS is negative
      have left_neg : 3 - x ^ 2 - 2 * x ^ 3 < 0 := by nlinarith
      -- but then the RHS is non-negaitve
      have right_pos : 0 ≤ |Real.cos (Real.pi * x) + x ^ 3 - 3 * x ^ 2 + 3 * x|
        := abs_nonneg _

      -- that's a contradiction
      linarith