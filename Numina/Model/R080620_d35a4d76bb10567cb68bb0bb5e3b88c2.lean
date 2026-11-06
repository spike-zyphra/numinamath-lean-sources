import Mathlib

theorem inequalities_129006 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^2 * b * (b - c) / (a + b) + b^2 * c * (c - a) / (b + c) + c^2 * a * (a - b) / (c + a) ≥ 0 := by
  have h1 : 0 < a + b := by linarith
  have h2 : 0 < b + c := by linarith
  have h3 : 0 < c + a := by linarith

  have h4 : a + b ≠ 0 := by linarith
  have h5 : b + c ≠ 0 := by linarith
  have h6 : c + a ≠ 0 := by linarith

  have h7 : (a + b) * (b + c) * (c + a) > 0 := by
    apply mul_pos
    · apply mul_pos
      · linarith
      · linarith
    · linarith
  
  have h8 : a^2 * b * (b - c) / (a + b) + b^2 * c * (c - a) / (b + c) + c^2 * a * (a - b) / (c + a) =
    (a^2 * b * (b - c) * (b + c) * (c + a) + b^2 * c * (c - a) * (a + b) * (c + a) + c^2 * a * (a - b) * (a + b) * (b + c)) / ((a + b) * (b + c) * (c + a)) := by 
    have h9 : a + b ≠ 0 := by linarith
    have h10 : b + c ≠ 0 := by linarith
    have h11 : c + a ≠ 0 := by linarith
    field_simp
    <;> ring

  rw [h8]
  apply div_nonneg
  -- Compute A_1, A_2, A_3 and prove they are non-negative
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), 
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
  ]
  -- Show that denominator is positive
  positivity