import Mathlib

theorem inequalities_91135 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c ≥ 1) :
    a ^ 4 + b ^ 3 + c ^ 2 ≥ a ^ 3 + b ^ 2 + c := by
  have h1 : 0 < a * b := by
    nlinarith
  have h2 : 0 < a * b * c := by
    positivity
  nlinarith [sq_nonneg (a^2 - a), sq_nonneg (b^2 - b), sq_nonneg (c^2 - c),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          sq_nonneg (a^2*(b - 1)), sq_nonneg (b^2*(c - 1)), sq_nonneg (c^2*(a - 1)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith)]