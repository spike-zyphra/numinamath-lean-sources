import Mathlib

theorem algebra_300464 (x y : ℝ) (h : x ^ 2 / 3 + y ^ 2 = 1) :
    |2 * x + y - 4| + |4 - x - 2 * y| ∈ Set.Icc 2 14 := by
  have h1 : 2 ≤ |2 * x + y - 4| + |4 - x - 2 * y| := by
    cases' abs_cases (2 * x + y - 4) with h11 h11 <;> 
      cases' abs_cases (4 - x - 2 * y) with h2 h2 <;> 
        nlinarith [sq_nonneg (x - 3 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (2 * x + 3 * y), sq_nonneg (x - 3 / 2), sq_nonneg (y + 1 / 2), h]
  have h2 : |2 * x + y - 4| + |4 - x - 2 * y| ≤ 14 := by
    cases' abs_cases (2 * x + y - 4) with h11 h11 <;> 
      cases' abs_cases (4 - x - 2 * y) with h2 h2 <;> 
        nlinarith [sq_nonneg (x - 3 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (2 * x + 3 * y), sq_nonneg (x - 3 / 2), sq_nonneg (y + 1 / 2), h]
  constructor
  · -- Show that 2 ≤ |2 * x + y - 4| + |4 - x - 2 * y|
    linarith [h1]
  · -- Show that |2 * x + y - 4| + |4 - x - 2 * y| ≤ 14
    linarith [h2]