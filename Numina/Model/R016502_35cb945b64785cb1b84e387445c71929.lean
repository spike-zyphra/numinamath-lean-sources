import Mathlib

/- Given real numbers $x$, $y$ satisfy $\frac{{{x}^{2}}}{3}+{{y}^{2}}=1$, then the range of values for $P=\left| 2x+y-4 \right|+\left| 4-x-2y \right|$ is ___          ___. -/
theorem algebra_12355 (x y : ℝ) (h : x^2/3 + y^2 = 1) :
    2 ≤ abs (2*x + y - 4) + abs (4 - x - 2*y) ∧
    abs (2*x + y - 4) + abs (4 - x - 2*y) ≤ 14 := by
  constructor
  · -- Prove that 2 ≤ abs (2*x + y - 4) + abs (4 - x - 2*y)
    cases' abs_cases (2*x + y - 4) with h1 h1 <;> 
      cases' abs_cases (4 - x - 2*y) with h2 h2 <;> 
      try { 
        nlinarith [sq_nonneg (x - 3/2), sq_nonneg (y - 1/2), sq_nonneg (x + 3/2), sq_nonneg (y + 1/2), 
          sq_nonneg (x^2/3 + y^2 - 1), 
          mul_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)]
      }
    all_goals
      try { 
        nlinarith [sq_nonneg (x - 3/2), sq_nonneg (y - 1/2), sq_nonneg (x + 3/2), sq_nonneg (y + 1/2), 
          sq_nonneg (x^2/3 + y^2 - 1)]
      }
      <;> try { 
        nlinarith 
      }
  · -- Prove that abs (2*x + y - 4) + abs (4 - x - 2*y) ≤ 14
    cases' abs_cases (2*x + y - 4) with h1 h1 <;> 
      cases' abs_cases (4 - x - 2*y) with h2 h2 <;> 
      try { 
        nlinarith [sq_nonneg (x + 3/2), sq_nonneg (y + 1/2), sq_nonneg (x - 3/2), sq_nonneg (y - 1/2), 
          sq_nonneg (x^2/3 + y^2 - 1), 
          mul_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)]
      }
    all_goals
      try { 
        nlinarith [sq_nonneg (x + 3/2), sq_nonneg (y + 1/2), sq_nonneg (x - 3/2), sq_nonneg (y - 1/2), 
          sq_nonneg (x^2/3 + y^2 - 1)]
      }
      <;> try { 
        nlinarith 
      }