import Mathlib

theorem inequalities_3305
    (a b m n : ℝ) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) (hn : 0 < n) :
    (2 * a * m + m ^ 2) * (2 * b * n + n ^ 2) ≤ (a * n + b * m + m * n) ^ 2 := by 
  nlinarith [sq_nonneg (a * n - b * m)]