import Mathlib

theorem inequalities_6112
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 3 / (a * b * c) ≥ 28 := by
  have pos1 : 0 < a * b * c := by positivity
  have pos2 : 0 < a ^ 2 + b ^ 2 + c ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have h1 : (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 3 / (a * b * c) - 28 ≥ 0 := by
    have pos2' : 0 < (a ^ 2 + b ^ 2 + c ^ 2) * (a * b * c) := by positivity
    have h2 : (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 3 / (a * b * c) - 28 =
      ((a * b + b * c + c * a) * (a * b * c) + (a + b + c) ^ 3 * (a ^ 2 + b ^ 2 + c ^ 2) - 28 * ((a ^ 2 + b ^ 2 + c ^ 2) * (a * b * c))) / ((a^ 2 + b^ 2 + c^ 2) * (a * b * c)) := by
      field_simp
      ring
    rw [h2] at *
    apply div_nonneg
    · -- Prove that the numerator is non-negative
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_pos (show 0 < a * b by positivity) (show 0 < c by linarith), 
        mul_pos (show 0 < a by linarith) (show 0 < b * c by positivity)
      ]
    · -- Prove that the denominator is positive
      positivity
  linarith