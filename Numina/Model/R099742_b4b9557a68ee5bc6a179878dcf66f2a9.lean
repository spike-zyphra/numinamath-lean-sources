import Mathlib

theorem algebra_301101 (x y : ℝ) (h : 2*x^2+x*y+2*y^2=2) :
    x^2-5*x*y+y^2 ∈ Set.Icc (-6/5) (14/3) := by
  constructor
  · -- To show $x^2-5xy+y^2 \geq -\frac{6}{5}$
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (2 * x + y), sq_nonneg (x - 2 * y)]
  · -- To show $x^2-5xy+y^2 \leq \frac{14}{3}$
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (2 * x + y), sq_nonneg (x - 2 * y)]