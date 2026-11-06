import Mathlib

theorem algebra_314186 {x y : ℝ} (h : x ^ 2 + y ^ 2 = 10 * x - 6 * y - 34) : x + y = 2 := by
  -- First, we rearrange the equation to make it easier to complete the square
  have h1 : (x - 5) ^ 2 + (y + 3) ^ 2 = 0 := by
    nlinarith
  -- Since both terms are non-negative, their sum can only be zero if both terms are zero
  have hx : (x - 5) ^ 2 = 0 := by
    linarith [sq_nonneg (x - 5), sq_nonneg (y + 3)]
  have hy : (y + 3) ^ 2 = 0 := by
    linarith [sq_nonneg (x - 5), sq_nonneg (y + 3)]
  -- If a square is zero, then the base must be zero
  have hx2 : x - 5 = 0 := by
    rwa [sq_eq_zero_iff] at hx
  have hy2 : y + 3 = 0 := by
    rwa [sq_eq_zero_iff] at hy
  -- Solving these equations gives us the values of x and y
  have hx1 : x = 5 := by
    linarith
  have hy1 : y = -3 := by
    linarith
  -- Therefore, x + y = 5 + (-3) = 2
  linarith [hx1, hy1]