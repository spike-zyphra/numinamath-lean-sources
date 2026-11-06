import Mathlib

theorem inequalities_62777 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a * (b ^ 2 + c ^ 2) / ((b + c) * (a ^ 2 + b * c)) +
            b * (c ^ 2 + a ^ 2) / ((c + a) * (b ^ 2 + c * a)) +
            c * (a ^ 2 + b ^ 2) / ((a + b) * (c ^ 2 + a * b)) := by
  have h1 : (b + c) * (a ^ 2 + b * c) > 0 := by positivity
  have h2 : (c + a) * (b ^ 2 + c * a) > 0 := by positivity
  have h3 : (a + b) * (c ^ 2 + a * b) > 0 := by positivity
  have h7 : a * (b ^ 2 + c ^ 2) / ((b + c) * (a ^ 2 + b * c)) +
          b * (c ^ 2 + a ^ 2) / ((c + a) * (b ^ 2 + c * a)) +
          c * (a ^ 2 + b ^ 2) / ((a + b) * (c ^ 2 + a * b)) - 3 / 2 ≥ 0 := by
    have h7 : a * (b ^ 2 + c ^ 2) / ((b + c) * (a ^ 2 + b * c)) +
          b * (c ^ 2 + a ^ 2) / ((c + a) * (b ^ 2 + c * a)) +
          c * (a ^ 2 + b ^ 2) / ((a + b) * (c ^ 2 + a * b)) - 3 / 2 =
          (a * (b ^ 2 + c ^ 2) * (c + a) * (b ^ 2 + c * a) * (a + b) * (c ^ 2 + a * b) +
          b * (c ^ 2 + a ^ 2) * (b + c) * (a ^ 2 + b * c) * (a + b) * (c ^ 2 + a * b) +
          c * (a ^ 2 + b ^ 2) * (b + c) * (a ^ 2 + b * c) * (c + a) * (b ^ 2 + c * a) -
          3 / 2 * ((b + c) * (a ^ 2 + b * c) * (c + a) * (b ^ 2 + c * a) * (a + b) * (c ^ 2 + a * b))) /
          ((b + c) * (a ^ 2 + b * c) * (c + a) * (b ^ 2 + c * a) * (a + b) * (c ^ 2 + a * b)) := by
      field_simp
      ring
    rw [h7]
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c), sq_nonneg (a * b - a * c),
      sq_nonneg (a * (b ^ 2 + c ^ 2) - b * (c ^ 2 + a ^ 2)), sq_nonneg (a * (b ^ 2 + c ^ 2) - c * (a ^ 2 + b ^ 2)), sq_nonneg (b * (c ^ 2 + a ^ 2) - c * (a ^ 2 + b ^ 2)), 
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    positivity
  linarith