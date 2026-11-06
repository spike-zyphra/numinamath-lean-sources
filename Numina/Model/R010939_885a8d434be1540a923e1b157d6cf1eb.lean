import Mathlib

theorem inequalities_201474 (a b c d : ℝ) :
    (a + b + c + d) * (a * b * (c + d) + (a + b) * c * d) - a * b * c * d ≤
    ((a * (b + d) + b * (c + d) + c * (d + a)) ^ 2) / 2 := by 
  nlinarith [sq_nonneg (a*b - b*c), sq_nonneg (b*c - c*d), sq_nonneg (c*d - d*a), sq_nonneg (d*a - a*b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
          sq_nonneg (a*b + c*d - (b*c + a*d)),
          sq_nonneg (a*b - c*d), sq_nonneg (b*c - d*a), sq_nonneg (c*d - a*b), sq_nonneg (d*a - b*c),
          sq_nonneg (a*b - b*c + c*d - d*a), sq_nonneg (a*b + b*c - c*d - d*a), sq_nonneg (a*c - b*d),
          sq_nonneg (a*d - b*c), sq_nonneg (a*b - c*d + b*c - a*d)]