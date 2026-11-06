import Mathlib

theorem inequalities_597751 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a * b + b * c + c * a = 3) :
    1 / (a ^ 2 + 2) + 1 / (b ^ 2 + 2) + 1 / (c ^ 2 + 2) ≤ 1 := by
  have h1 : 0 < a ^ 2 + 2 := by nlinarith
  have h2 : 0 < b ^ 2 + 2 := by nlinarith
  have h3 : 0 < c ^ 2 + 2 := by nlinarith
  have h4 : 1 / (a ^ 2 + 2) + 1 / (b ^ 2 + 2) + 1 / (c ^ 2 + 2) - 1 ≤ 0 := by
    have h5 : 1 / (a ^ 2 + 2) + 1 / (b ^ 2 + 2) + 1 / (c ^ 2 + 2) - 1 =
        ((b^2 + 2) * (c^2 + 2) + (a^2 + 2) * (c^2 + 2) + (a^2 + 2) * (b^2 + 2) - (a^2 + 2) * (b^2 + 2) * (c^2 + 2)) / ((a^2 + 2) * (b^2 + 2) * (c^2 + 2)) := by
      field_simp
      ring
    rw [h5] at *
    have h6 : (b^2 + 2) * (c^2 + 2) + (a^2 + 2) * (c^2 + 2) + (a^2 + 2) * (b^2 + 2) - (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ≤ 0 := by
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * b + b * c + c * a - 3), sq_nonneg (a * b * c - 1),
        mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
    have h7 : ((b^2 + 2) * (c^2 + 2) + (a^2 + 2) * (c^2 + 2) + (a^2 + 2) * (b^2 + 2) - (a^2 + 2) * (b^2 + 2) * (c^2 + 2)) / ((a^2 + 2) * (b^2 + 2) * (c^2 + 2)) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      linarith
      positivity
    linarith
  linarith