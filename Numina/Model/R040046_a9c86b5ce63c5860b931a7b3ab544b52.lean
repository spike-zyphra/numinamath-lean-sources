import Mathlib

theorem inequalities_159475 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^4 + b^4 + c^4 = 3) :
    1 / (4 - a * b) + 1 / (4 - b * c) + 1 / (4 - c * a) ≤ 1 := by
  have h1 : 0 < 4 - a * b := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a ^ 2 - 1), sq_nonneg (b ^ 2 - 1), sq_nonneg (c ^ 2 - 1),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h2 : 0 < 4 - b * c := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a ^ 2 - 1), sq_nonneg (b ^ 2 - 1), sq_nonneg (c ^ 2 - 1),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h3 : 0 < 4 - c * a := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a ^ 2 - 1), sq_nonneg (b ^ 2 - 1), sq_nonneg (c ^ 2 - 1),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h4 : 1 / (4 - a * b) + 1 / (4 - b * c) + 1 / (4 - c * a) - 1 ≤ 0 := by
    have h5 : 0 < (4 - a * b) * (4 - b * c) * (4 - c * a) := by
      positivity
    have h6 : (1 / (4 - a * b) + 1 / (4 - b * c) + 1 / (4 - c * a) - 1) =
        ((4 - b * c) * (4 - c * a) + (4 - a * b) * (4 - c * a) + (4 - a * b) * (4 - b * c) - (4 - a * b) * (4 - b * c) * (4 - c * a)) / ((4 - a * b) * (4 - b * c) * (4 - c * a)) := by
      field_simp
      <;> ring
    rw [h6] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show numerator is ≤ 0
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a ^ 2 + b ^ 2 + c ^ 2 - 3),
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b * c by nlinarith [mul_pos hb hc]),
          mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ a * c by nlinarith [mul_pos ha hc]),
          mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ a * b by nlinarith [mul_pos ha hb]),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (a * b + b * c + c * a - 3)]
    · -- Show denominator is ≥ 0
      positivity
  linarith