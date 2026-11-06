import Mathlib

theorem algebra_40807 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 4*a*b*c*(a+b+c) = (a+b)^2*(a+c)^2) : a*(a+b+c) = b*c := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a*(a + b + c) - b*c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]