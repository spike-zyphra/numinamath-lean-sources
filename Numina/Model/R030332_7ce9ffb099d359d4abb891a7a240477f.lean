import Mathlib

theorem inequalities_598048 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    9 / (a + b + c) ≤ 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) := by

  have h1 : 0 < a + b + c := by linarith
  have h2 : 0 < a + b := by linarith
  have h3 : 0 < b + c := by linarith
  have h4 : 0 < c + a := by linarith

  have h5 : 9 / (a + b + c) - 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) ≤ 0 := by
    have pos1 : 0 < a + b + c := h1
    have pos2 : 0 < a + b := h2
    have pos3 : 0 < b + c := h3
    have pos4 : 0 < c + a := h4

    have h6 : 9 * (a + b) * (b + c) * (c + a) - 2 * ( (a + b + c) * (b + c) * (c + a) + (a + b + c) * (a + b) * (c + a) + (a + b + c) * (a + b) * (b + c) ) ≤ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    
    have eq : 9 / (a + b + c) - 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) =
        (9 * (a + b) * (b + c) * (c + a) - 2 * ( (a + b + c) * (b + c) * (c + a) + (a + b + c) * (a + b) * (c + a) + (a + b + c) * (a + b) * (b + c) )) / ((a + b + c) * (a + b) * (b + c) * (c + a)) := by
      field_simp
      <;> ring
    rw [eq] at *
  
    apply div_nonpos_of_nonpos_of_nonneg
    linarith [h6]
    positivity
  
  linarith