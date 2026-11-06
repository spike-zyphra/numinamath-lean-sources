import Mathlib

theorem inequalities_289457 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ((a + 1)^2 / b + (b + 1)^2 / a) ≥ 8 := by
  have pos1 : 0 < a * b := mul_pos ha hb
  have h1 : (a + 1) ^ 2 / b + (b + 1) ^ 2 / a - 8 ≥ 0 := by
    have h2 : a * b > 0 := mul_pos ha hb
    have h3 : (a + 1) ^ 2 / b + (b + 1) ^ 2 / a - 8 = ((a + 1) ^ 2 * a - 8 * (a * b) + (b + 1) ^ 2 * b) / (a * b) := by
      field_simp [show 0 < b by linarith, show 0 < a by linarith]
      <;> ring_nf <;> nlinarith
    rw [h3]
    have h4 : ((a + 1) ^ 2 * a - 8 * (a * b) + (b + 1) ^ 2 * b) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a * b - 1),
        sq_nonneg (a - 2 * b), sq_nonneg (b - 2 * a),
        mul_pos ha hb, mul_nonneg (show 0 ≤ a by linarith [ha]) (show 0 ≤ b by linarith [hb])
      ]
    apply div_nonneg
    linarith
    all_goals nlinarith
  linarith