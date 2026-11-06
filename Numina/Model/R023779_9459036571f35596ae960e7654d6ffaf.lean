import Mathlib

theorem algebra_358: IsGreatest {(x - y) ^ 2 | (x : ℝ) (y : ℝ) (_ : x ^ 2 + x * y + y ^ 2 = 3)} 12 := by
  constructor
  · -- Show 12 is in the set.
    use Real.sqrt 3, -Real.sqrt 3, by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    all_goals
      norm_num
      <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  · -- Show 12 is the greatest element in the set.
    intro r hr
    rcases hr with ⟨x, y, h, hr⟩
    have h1 : x ^ 2 + x * y + y ^ 2 = 3 := h
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x - 2 * y), sq_nonneg (2 * x - y), sq_nonneg (x^2 - y^2)]