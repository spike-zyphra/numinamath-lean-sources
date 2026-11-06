import Mathlib

theorem inequalities_110996 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * (a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b)) ≥ a + b + c := by
  have pos1 : 0 < b + c := by nlinarith
  have pos2 : 0 < c + a := by nlinarith
  have pos3 : 0 < a + b := by nlinarith
  
  have h1 : 2 * (a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b)) - (a + b + c) ≥ 0 := by 
    have h2 : 2 * (a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b)) - (a + b + c) =
        (2 * a ^ 2 * (c + a) * (a + b) + 2 * b ^ 2 * (b + c) * (a + b) + 2 * c ^ 2 * (b + c) * (c + a)
        - (a * (b + c) * (c + a) * (a + b) + b * (b + c) * (c + a) * (a + b) + c * (b + c) * (c + a) * (a + b))
        ) / ((b + c) * (c + a) * (a + b)) := by
      field_simp [pos1, pos2, pos3]
      ring
    rw [h2]

    have pos4 : 0 < (b + c) * (c + a) * (a + b) := by
      positivity

    have h3 : 2 * a ^ 2 * (c + a) * (a + b) + 2 * b ^ 2 * (b + c) * (a + b) + 2 * c ^ 2 * (b + c) * (c + a)
      - (a * (b + c) * (c + a) * (a + b) + b * (b + c) * (c + a) * (a + b) + c * (b + c) * (c + a) * (a + b)) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

    apply div_nonneg
    linarith
    all_goals positivity
  
  linarith