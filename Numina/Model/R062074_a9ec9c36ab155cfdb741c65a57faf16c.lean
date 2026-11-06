import Mathlib

theorem inequalities_318118
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    (a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b)) ≥
    ((1 : ℝ) / 2) * (a + b + c) := by 
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + a := by linarith
  have h3 : 0 < a + b := by linarith
  have h4 : a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) - ((1 : ℝ) / 2) * (a + b + c) ≥ 0 := by 
    have h5 : (a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) - ((1 : ℝ) / 2) * (a + b + c)) =
          (a ^ 2 * (c + a) * (a + b) + b ^ 2 * (b + c) * (a + b) + c ^ 2 * (b + c) * (c + a) - (1 / 2) * (a + b + c) * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [h5] at *
    have h6 : (a ^ 2 * (c + a) * (a + b) + b ^ 2 * (b + c) * (a + b) + c ^ 2 * (b + c) * (c + a) - (1 / 2) * (a + b + c) * (b + c) * (c + a) * (a + b)) ≥ 0 := by 
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have h7 : (b + c) * (c + a) * (a + b) > 0 := by 
      positivity
    apply div_nonneg 
    linarith 
    all_goals positivity 
  linarith