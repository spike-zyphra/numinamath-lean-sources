import Mathlib

theorem algebra_299505 :
    IsLeast {2 * x ^ 2 + 4 * x * y + 5 * y ^ 2 - 4 * x + 2 * y - 5 | (x : ℝ) (y : ℝ)} (-10) := by
  constructor
  · -- First, prove that -10 is in the set.
    use 2, -1
    norm_num
  · -- Then, prove that -10 is the smallest value in the set.
    rintro z ⟨x, y, hx⟩
    have h1 : 2 * x ^ 2 + 4 * x * y + 5 * y ^ 2 - 4 * x + 2 * y - 5 ≥ -10 := by
      nlinarith [sq_nonneg (x + y - 1), sq_nonneg (y + 1)]
    linarith [hx, h1]