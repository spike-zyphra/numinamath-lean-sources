import Mathlib
/- If $a, b, x$, and $y$ are real numbers such that $a x+b y=3, a x^{2}+b y^{2}=7, a x^{3}+b y^{3}=16$, and $a x^{4}+b y^{4}=42$, find $a x^{5}+b y^{5}$. -/
theorem algebra_608470 (a b x y : ℝ) (h1 : a * x + b * y = 3) (h2 : a * x ^ 2 + b * y ^ 2 = 7) (h3 : a * x ^ 3 + b * y ^ 3 = 16) (h4 : a * x ^ 4 + b * y ^ 4 = 42) : a * x ^ 5 + b * y ^ 5 = 20:= by
  -- use linear combination to solve the problem
  linear_combination
    38 * x * y * h1 + (-(14 * x * y) - 38 * x - 38 * y) * h2 +
        (-(1 * x * y) + 14 * x + 14 * y + 38) * h3 +
      (x + y - 14) * h4
