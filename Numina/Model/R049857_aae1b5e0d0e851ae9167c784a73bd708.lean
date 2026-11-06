import Mathlib

theorem inequalities_1724 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    33 ≤ 2*(a^3+b^3+c^3) / (a*b*c) + 9*(a+b+c)^2 / (a^2+b^2+c^2) := by
  have h1 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  have h2 : 0 < a^2 + b^2 + c^2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]

  have h3 : 2 * (a^3 + b^3 + c^3) / (a * b * c) + 9 * (a + b + c)^2 / (a^2 + b^2 + c^2) - 33 ≥ 0 := by 
    have h4 : 2 * (a^3 + b^3 + c^3) / (a * b * c) + 9 * (a + b + c)^2 / (a^2 + b^2 + c^2) - 33 =
          (2 * (a^3 + b^3 + c^3) * (a^2 + b^2 + c^2) + 9 * (a * b * c) * (a + b + c)^2 - 33 * (a * b * c) * (a^2 + b^2 + c^2)) / ((a * b * c) * (a^2 + b^2 + c^2)) := by
      field_simp [h1.ne.symm, h2.ne.symm]
      <;> ring
    rw [h4]
    have h5 : 2 * (a^3 + b^3 + c^3) * (a^2 + b^2 + c^2) + 9 * (a * b * c) * (a + b + c)^2 - 33 * (a * b * c) * (a^2 + b^2 + c^2) ≥ 0 := by 
      nlinarith [sq_nonneg (a^3 + b^3 + c^3 - 3 * a * b * c),
        sq_nonneg (a^2 + b^2 + c^2 - a * b - b * c - c * a),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2),
        sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (a + b + c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
        sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (b * c - c * a),
        sq_nonneg (a^3 - b^3), sq_nonneg (a^3 - c^3), sq_nonneg (b^3 - c^3)]
    apply div_nonneg h5
    positivity
  
  linarith