import Mathlib

open Real

theorem algebra_22111 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    4 / 3 ≤ a / (b + c + d) + b / (a + c + d) + c / (a + b + d) + d / (a + b + c) := by
  have h1 : b + c + d = 1 - a := by linarith
  have h2 : a + c + d = 1 - b := by linarith
  have h3 : a + b + d = 1 - c := by linarith
  have h4 : a + b + c = 1 - d := by linarith
  have pos1 : b + c + d > 0 := by nlinarith
  have pos2 : a + c + d > 0 := by nlinarith
  have pos3 : a + b + d > 0 := by nlinarith
  have pos4 : a + b + c > 0 := by nlinarith
  have h5 : a / (b + c + d) + b / (a + c + d) + c / (a + b + d) + d / (a + b + c) - 4 / 3 ≥ 0 := by
    have h6 : a / (b + c + d) + b / (a + c + d) + c / (a + b + d) + d / (a + b + c) - 4 / 3 =
        ( (a * (a + c + d) * (a + b + d) * (a + b + c) ) +
          (b * (b + c + d) * (a + b + d) * (a + b + c) ) +
          (c * (b + c + d) * (a + c + d) * (a + b + c) ) +
          (d * (b + c + d) * (a + c + d) * (a + b + d) ) - 
          (4 / 3) * (b + c + d) * (a + c + d) * (a + b + d) * (a + b + c) ) / 
          ( (b + c + d) * (a + c + d) * (a + b + d) * (a + b + c) ) := by
      field_simp
      ring
    rw [h6]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
          sq_nonneg (a + b + c + d - 4 / 3), 
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]
    positivity
  linarith