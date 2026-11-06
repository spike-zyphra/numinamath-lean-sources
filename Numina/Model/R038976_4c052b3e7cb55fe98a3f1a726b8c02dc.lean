import Mathlib

theorem algebra_7010 {a b c : ℝ} (h : a^3 + b^3 + c^3 = (a + b + c)^3) :
    a^5 + b^5 + c^5 = (a + b + c)^5 := by 
  have eq1 : a * b * c = (a * b + a * c + b * c) * (a + b + c) := by 
    nlinarith [sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c),
      sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have eq2 : a^5 + b^5 + c^5 = (a + b + c)^5 := by 
    nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b))]
  linarith