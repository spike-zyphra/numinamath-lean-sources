import Mathlib

theorem inequalities_604082 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / ((a + 1) * (a + 2)) + 1 / ((b + 1) * (b + 2)) +
    1 / ((c + 1) * (c + 2)) ≥ 1 / 2 := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals
      positivity
  have h10 : 0 < (a + 1) * (a + 2) * (b + 1) * (b + 2) * (c + 1) * (c + 2) := by
    positivity

  have h7 : 1 / ((a + 1) * (a + 2)) + 1 / ((b + 1) * (b + 2)) + 1 / ((c + 1) * (c + 2)) - 1 / 2 ≥ 0 := by
    have h8 : 1 / ((a + 1) * (a + 2)) + 1 / ((b + 1) * (b + 2)) + 1 / ((c + 1) * (c + 2)) - 1 / 2 =
        (2 * ((b + 1) * (b + 2) * (c + 1) * (c + 2)) + 2 * ((a + 1) * (a + 2) * (c + 1) * (c + 2)) + 2 * ((a + 1) * (a + 2) * (b + 1) * (b + 2)) - ((a + 1) * (a + 2) * (b + 1) * (b + 2) * (c + 1) * (c + 2)) ) / (2 * ((a + 1) * (a + 2) * (b + 1) * (b + 2) * (c + 1) * (c + 2)) ) := by 
      field_simp
      ring
    rw [h8]
    have h2 : 2 * ((b + 1) * (b + 2) * (c + 1) * (c + 2)) + 2 * ((a + 1) * (a + 2) * (c + 1) * (c + 2)) + 2 * ((a + 1) * (a + 2) * (b + 1) * (b + 2)) - ((a + 1) * (a + 2) * (b + 1) * (b + 2) * (c + 1) * (c + 2)) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        sq_nonneg (a * b + a * c + b * c - 3),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc]

    have h12 : (2 * ((b + 1) * (b + 2) * (c + 1) * (c + 2)) + 2 * ((a + 1) * (a + 2) * (c + 1) * (c + 2)) + 2 * ((a + 1) * (a + 2) * (b + 1) * (b + 2)) - ((a + 1) * (a + 2) * (b + 1) * (b + 2) * (c + 1) * (c + 2)) ) / (2 * ((a + 1) * (a + 2) * (b + 1) * (b + 2) * (c + 1) * (c + 2)) ) ≥ 0 := by
      apply div_nonneg
      · linarith
      · positivity

    linarith

  linarith