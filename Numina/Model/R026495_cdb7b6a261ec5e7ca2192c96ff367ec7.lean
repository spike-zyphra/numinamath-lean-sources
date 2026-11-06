import Mathlib

theorem inequalities_37730 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / a + 1 / b + 1 / c = 1) :
    3 * (a * b + b * c + c * a) + 9 / (a + b + c) ≤
    9 * a * b * c / (a + b + c) + 2 * (a ^ 2 + b ^ 2 + c ^ 2) + 1 := by
  have h1 : a * b + b * c + c * a = a * b * c := by
    field_simp at h
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h2 : 0 < a + b + c := by
    linarith
  have h4 : 0 < a + b + c := by
    linarith

  have h5 : 3 * (a * b + b * c + c * a) + 9 / (a + b + c) ≤ 9 * a * b * c / (a + b + c) + 2 * (a ^ 2 + b ^ 2 + c ^ 2) + 1 := by
    have h6 : 0 < a + b + c := by
      linarith
    have h7 : 3 * (a * b + b * c + c * a) * (a + b + c) + 9 ≤ 9 * a * b * c + 2 * (a ^ 2 + b ^ 2 + c ^ 2) * (a + b + c) + (a + b + c) := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        h1]
    have h12 : 3 * (a * b + b * c + c * a) + 9 / (a + b + c) - (9 * a * b * c / (a + b + c) + 2 * (a ^ 2 + b ^ 2 + c ^ 2) + 1) ≤ 0 := by
      have h13 : 0 < a + b + c := by linarith
      have h14 : (3 * (a * b + b * c + c * a) + 9 / (a + b + c) - (9 * a * b * c / (a + b + c) + 2 * (a ^ 2 + b ^ 2 + c ^ 2) + 1)) = ((3 * (a * b + b * c + c * a) * (a + b + c) + 9) - (9 * a * b * c + 2 * (a ^ 2 + b ^ 2 + c ^ 2) * (a + b + c) + (a + b + c))) / (a + b + c) := by
        field_simp
        <;> ring
      rw [h14]
      apply div_nonpos_of_nonpos_of_nonneg
      linarith
      linarith
    linarith
  linarith