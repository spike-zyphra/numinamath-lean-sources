import Mathlib

theorem algebra_322517 (x y : ℝ) (h : x^2 + x * y + y^2 = 3) :
    x^2 - x * y + y^2 ∈ Set.Icc 1 9 := by 
  constructor
  · -- Let's prove the lower bound, that is, $1 \leq x^2 - x \cdot y + y^2$
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x - y - 2),
      sq_nonneg (x + y + 2), sq_nonneg (x - y + 2)]
  · -- Let's prove the upper bound, that is, $x^2 - x \cdot y + y^2 \leq 9$
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x - y - 2),
      sq_nonneg (x + y + 2), sq_nonneg (x - y + 2)]