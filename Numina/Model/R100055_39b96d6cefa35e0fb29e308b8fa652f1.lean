import Mathlib

theorem inequalities_6567 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    1 / (a + 2 * b + 3 * c) + 1 / (b + 2 * c + 3 * a) +
    1 / (c + 2 * a + 3 * b) ≤ 1 / (6 * a) + 1 / (6 * b) + 1 / (6 * c) := by
  have ha2 : 0 < a := by linarith
  have hb2 : 0 < b := by linarith
  have hc2 : 0 < c := by linarith
  have h1 : 0 < a + 2 * b + 3 * c := by
    nlinarith [h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h2 : 0 < b + 2 * c + 3 * a := by
    nlinarith [h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h3 : 0 < c + 2 * a + 3 * b := by
    nlinarith [h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h4 : 0 < 6 * a := by nlinarith
  have h5 : 0 < 6 * b := by nlinarith
  have h6 : 0 < 6 * c := by nlinarith
  have h7 : 0 < (a + 2 * b + 3 * c) * (b + 2 * c + 3 * a) * (c + 2 * a + 3 * b) := by
    positivity
  have h8 : 0 < (a + 2 * b + 3 * c) * (b + 2 * c + 3 * a) * (c + 2 * a + 3 * b) * (6 * a) * (6 * b) * (6 * c) := by
    positivity
  have h9 : a + b + c = 1 := h
  have h10 : 1 / (a + 2 * b + 3 * c) + 1 / (b + 2 * c + 3 * a) + 1 / (c + 2 * a + 3 * b) - (1 / (6 * a) + 1 / (6 * b) + 1 / (6 * c)) ≤ 0 := by
    have h11 : 1 / (a + 2 * b + 3 * c) + 1 / (b + 2 * c + 3 * a) + 1 / (c + 2 * a + 3 * b) - (1 / (6 * a) + 1 / (6 * b) + 1 / (6 * c)) =
        ( (b + 2 * c + 3 * a) * (c + 2 * a + 3 * b) * (6 * a) * (6 * b) * (6 * c) +
          (a + 2 * b + 3 * c) * (c + 2 * a + 3 * b) * (6 * a) * (6 * b) * (6 * c) +
          (a + 2 * b + 3 * c) * (b + 2 * c + 3 * a) * (6 * a) * (6 * b) * (6 * c) -
          ( (a + 2 * b + 3 * c) * (b + 2 * c + 3 * a) * (c + 2 * a + 3 * b) * (6 * b) * (6 * c) +
            (a + 2 * b + 3 * c) * (b + 2 * c + 3 * a) * (c + 2 * a + 3 * b) * (6 * a) * (6 * c) +
            (a + 2 * b + 3 * c) * (b + 2 * c + 3 * a) * (c + 2 * a + 3 * b) * (6 * a) * (6 * b) ) ) /
        ( (a + 2 * b + 3 * c) * (b + 2 * c + 3 * a) * (c + 2 * a + 3 * b) * (6 * a) * (6 * b) * (6 * c) ) := by
      field_simp
      ring
    rw [h11]
    have h12 : (b + 2 * c + 3 * a) * (c + 2 * a + 3 * b) * (6 * a) * (6 * b) * (6 * c) +
      (a + 2 * b + 3 * c) * (c + 2 * a + 3 * b) * (6 * a) * (6 * b) * (6 * c) +
      (a + 2 * b + 3 * c) * (b + 2 * c + 3 * a) * (6 * a) * (6 * b) * (6 * c) -
      ( (a + 2 * b + 3 * c) * (b + 2 * c + 3 * a) * (c + 2 * a + 3 * b) * (6 * b) * (6 * c) +
        (a + 2 * b + 3 * c) * (b + 2 * c + 3 * a) * (c + 2 * a + 3 * b) * (6 * a) * (6 * c) +
        (a + 2 * b + 3 * c) * (b + 2 * c + 3 * a) * (c + 2 * a + 3 * b) * (6 * a) * (6 * b) ) ≤ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    apply div_nonpos_of_nonpos_of_nonneg h12 (by positivity)
  linarith