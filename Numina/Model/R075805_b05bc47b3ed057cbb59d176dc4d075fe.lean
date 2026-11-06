import Mathlib

theorem inequalities_277017 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hne : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    (a + b + c) * (1 / a + 1 / b + 1 / c) > 9 := by
  have hab : 0 < a * b := mul_pos ha hb
  have hbc : 0 < b * c := mul_pos hb hc
  have hac : 0 < a * c := mul_pos ha hc
  have h1 : 0 < a * b * c := mul_pos hab hc
  have h2 : (a + b + c) * (1 / a + 1 / b + 1 / c) - 9 > 0 := by
    have h3 : (a + b + c) * (1 / a + 1 / b + 1 / c) - 9 =
          ((a + b + c) * (a * b + b * c + c * a) - 9 * (a * b * c)) / (a * b * c) := by
      field_simp [ha.ne.symm, hb.ne.symm, hc.ne.symm]
      ring
    rw [h3]
    apply div_pos
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne hne.1),
          sq_pos_of_ne_zero (sub_ne_zero_of_ne hne.2.1),
          sq_pos_of_ne_zero (sub_ne_zero_of_ne hne.2.2),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    positivity
  linarith