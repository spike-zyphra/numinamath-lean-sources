import Mathlib

/- If $x$ and $y$ are real numbers such that $x^{2013}+y^{2013}>x^{2012}+y^{2012}$, prove that $x^{2014}+y^{2014}>x^{2013}+y^{2013}$ -/
theorem inequalities_30456 (x y : ℝ) (h : x^2013 + y^2013 > x^2012 + y^2012) :
    x^2014 + y^2014 > x^2013 + y^2013 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1),
    pow_nonneg (sq_nonneg x) 1006, pow_nonneg (sq_nonneg y) 1006]
  <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1),
    pow_nonneg (sq_nonneg x) 1006, pow_nonneg (sq_nonneg y) 1006]
  <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1),
    pow_nonneg (sq_nonneg x) 1006, pow_nonneg (sq_nonneg y) 1006]