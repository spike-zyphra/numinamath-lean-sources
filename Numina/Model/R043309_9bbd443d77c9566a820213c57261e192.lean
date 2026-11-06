import Mathlib

theorem inequalities_2868
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    (b + c) / a + (c + a) / b + (a + b) / c ≥
    a / (b + c) + b / (c + a) + c / (a + b) + 9 / 2 := by
  have h1 : 0 < a * b * c * (b + c) * (c + a) * (a + b) := by
    positivity
  have h2 : (b + c) / a + (c + a) / b + (a + b) / c - (a / (b + c) + b / (c + a) + c / (a + b) + 9 / 2) ≥ 0 := by
    have h3 : (b + c) / a + (c + a) / b + (a + b) / c - (a / (b + c) + b / (c + a) + c / (a + b) + 9 / 2) =
          ( (b + c) * (b * c * (b + c) * (c + a) * (a + b)) +
            (c + a) * (a * c * (b + c) * (c + a) * (a + b)) +
            (a + b) * (a * b * (b + c) * (c + a) * (a + b)) - 
            (a * (a * b * c * (c + a) * (a + b)) ) - 
            (b * (a * b * c * (b + c) * (a + b)) ) - 
            (c * (a * b * c * (b + c) * (c + a)) ) - 
            ( (9 / 2) * a * b * c * (b + c) * (c + a) * (a + b) ) ) / ( a * b * c * (b + c) * (c + a) * (a + b) ) := by 
      field_simp
      ring
    rw [h3] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
        sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos hb hc, 
        mul_pos ha hc, 
        mul_pos (show 0 < b * c from mul_pos hb hc) (show 0 < a from ha), 
        mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < c from hc), 
        mul_pos (show 0 < a * c from mul_pos ha hc) (show 0 < b from hb) ]
    all_goals positivity
  linarith