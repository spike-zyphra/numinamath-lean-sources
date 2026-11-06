import Mathlib


theorem inequalities_600680 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a + b + c ≤ a * b / (a + b) + b * c / (b + c) + c * a / (c + a) +
      (a * b / c + b * c / a + c * a / b) / 2 := by

  have h1 : 0 < a + b := by nlinarith
  have h2 : 0 < b + c := by nlinarith
  have h3 : 0 < c + a := by nlinarith
  have ha1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have h7 : a + b + c - (a * b / (a + b) + b * c / (b + c) + c * a / (c + a) + (a * b / c + b * c / a + c * a / b) / 2) ≤ 0 := by
    have pos1 : 0 < (a + b) * (b + c) * (c + a) * (a * b * c) := by
      positivity

    have h8 : a + b + c - (a * b / (a + b) + b * c / (b + c) + c * a / (c + a) + (a * b / c + b * c / a + c * a / b) / 2) =
        ( (a + b + c) * (a + b) * (b + c) * (c + a) * (a * b * c) - (a * b * (b + c) * (c + a) * (a * b * c)) - (b * c * (a + b) * (c + a) * (a * b * c)) - (c * a * (a + b) * (b + c) * (a * b * c)) - (1/2) * (a * b * (a + b) * (b + c) * (c + a) * (a * b) + b * c * (a + b) * (b + c) * (c + a) * (b * c) + c * a * (a + b) * (b + c) * (c + a) * (c * a)) ) / ((a + b) * (b + c) * (c + a) * (a * b * c)) := by
      field_simp
      ring

    rw [h8]

    have h9 : (a + b + c) * (a + b) * (b + c) * (c + a) * (a * b * c) - (a * b * (b + c) * (c + a) * (a * b * c)) - (b * c * (a + b) * (c + a) * (a * b * c)) - (c * a * (a + b) * (b + c) * (a * b * c)) - (1/2) * (a * b * (a + b) * (b + c) * (c + a) * (a * b) + b * c * (a + b) * (b + c) * (c + a) * (b * c) + c * a * (a + b) * (b + c) * (c + a) * (c * a)) ≤ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
        sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
        mul_pos (mul_pos ha hb) hc, 
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        sq_nonneg (a * (a * b - b * c)), sq_nonneg (b * (a * b - b * c)), 
        sq_nonneg (b * (b * c - c * a)), sq_nonneg (c * (b * c - c * a)), 
        sq_nonneg (c * (c * a - a * b)), sq_nonneg (a * (c * a - a * b))
      ]

    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · positivity

  linarith