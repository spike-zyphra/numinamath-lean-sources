import Mathlib

theorem algebra_177898 (x y : ℝ) (h : x^2 * y^2 + x^2 - 10 * x * y - 8 * x + 16 = 0) :
    x * y ∈ Set.Icc 0 10 := by 
  constructor
  · -- Show that 0 ≤ x * y
    nlinarith [sq_nonneg (x * y - 5), sq_nonneg (x - 4), sq_nonneg (x * (y - 0)), sq_nonneg (y * x - 5), sq_nonneg ((x * y - 5) * (x * y - 5)), sq_nonneg ((x - 4) * (x * y - 5)), sq_nonneg (x * 0 - 0), sq_nonneg (y * 0 - 0)]
  · -- Show that x * y ≤ 10
    nlinarith [sq_nonneg (x * y - 5), sq_nonneg (x - 4), sq_nonneg (x * (y - 0)), sq_nonneg (y * x - 5), sq_nonneg ((x * y - 5) * (x * y - 5)), sq_nonneg ((x - 4) * (x * y - 5)), sq_nonneg (x * 0 - 0), sq_nonneg (y * 0 - 0)]