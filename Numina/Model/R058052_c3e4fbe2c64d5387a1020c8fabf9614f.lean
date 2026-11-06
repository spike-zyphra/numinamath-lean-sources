import Mathlib

theorem inequalities_601956 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / 2 ≤ 1 / ((a + 1) * (a + 2)) + 1 / ((b + 1) * (b + 2)) +
    1 / ((c + 1) * (c + 2)) := by
  have h3 : 0 < (a + 1) * (a + 2) := by
    apply mul_pos
    all_goals linarith
  have h4 : 0 < (b + 1) * (b + 2) := by
    apply mul_pos
    all_goals linarith
  have h5 : 0 < (c + 1) * (c + 2) := by
    apply mul_pos
    all_goals linarith
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : 0 < (a + 1) * (a + 2) * (b + 1) * (b + 2) * (c + 1) * (c + 2) := by
    positivity
  suffices 1 / 2 ≤ 1 / ((a + 1) * (a + 2)) + 1 / ((b + 1) * (b + 2)) + 1 / ((c + 1) * (c + 2)) by linarith
  have h6 : 1 / ((a + 1) * (a + 2)) + 1 / ((b + 1) * (b + 2)) + 1 / ((c + 1) * (c + 2)) - 1 / 2 ≥ 0 := by
    have h7 : 1 / ((a + 1) * (a + 2)) + 1 / ((b + 1) * (b + 2)) + 1 / ((c + 1) * (c + 2)) - 1 / 2 =
        (2 * ( (b + 1) * (b + 2) * (c + 1) * (c + 2) + (a + 1) * (a + 2) * (c + 1) * (c + 2) + (a + 1) * (a + 2) * (b + 1) * (b + 2) ) - (a + 1) * (a + 2) * (b + 1) * (b + 2) * (c + 1) * (c + 2)) /
        (2 * (a + 1) * (a + 2) * (b + 1) * (b + 2) * (c + 1) * (c + 2)) := by
      field_simp
      ring
    rw [h7]
    have h8 : 2 * ( (b + 1) * (b + 2) * (c + 1) * (c + 2) + (a + 1) * (a + 2) * (c + 1) * (c + 2) + (a + 1) * (a + 2) * (b + 1) * (b + 2) ) - (a + 1) * (a + 2) * (b + 1) * (b + 2) * (c + 1) * (c + 2) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc]
    apply div_nonneg
    linarith
    positivity
  linarith