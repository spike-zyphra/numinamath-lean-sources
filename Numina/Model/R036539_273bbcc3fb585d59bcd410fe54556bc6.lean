import Mathlib
theorem inequalities_202307 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    (a ^ 2 + b ^ 2 + c ^ 2) * (a / (b + c) + b / (c + a) + c / (a + b)) ≥ 1 / 2 := by
  have h1 : a ^ 2 + b ^ 2 + c ^ 2 ≥ 1 / 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h2 : a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
    have h3 : 0 < b + c := by
      linarith
    have h4 : 0 < c + a := by 
      linarith
    have h5 : 0 < a + b := by
      linarith
    have h6 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by 
      have h7 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
          ( a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 3 / 2 * (b + c) * (c + a) * (a + b) ) / ( (b + c) * (c + a) * (a + b) ) := by
        field_simp
        ring
      rw [h7]
      apply div_nonneg
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg ( (a - b) ), sq_nonneg ( (a - c) ), sq_nonneg ( (b - c) )
          ]
      positivity
    linarith 
  nlinarith [h1, h2, mul_pos (show 0 < a ^ 2 + b ^ 2 + c ^ 2 by nlinarith) (show 0 < a / (b + c) + b / (c + a) + c / (a + b) by positivity) ]