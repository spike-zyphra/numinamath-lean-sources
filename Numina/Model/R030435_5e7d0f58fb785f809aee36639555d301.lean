import Mathlib

theorem inequalities_313333 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a / (a ^ 2 + 2) + b / (b ^ 2 + 2) + c / (c ^ 2 + 2) ≤ 1 := by 
  have h1 : 0 < a ^ 2 + 2 := by nlinarith
  have h2 : 0 < b ^ 2 + 2 := by nlinarith
  have h3 : 0 < c ^ 2 + 2 := by nlinarith
  have h4 : a / (a ^ 2 + 2) + b / (b ^ 2 + 2) + c / (c ^ 2 + 2) - 1 ≤ 0 := by
    have h5 : a / (a ^ 2 + 2) + b / (b ^ 2 + 2) + c / (c ^ 2 + 2) - 1 =
        ( (a * (b^2 + 2) * (c^2 + 2) + b * (a^2 + 2) * (c^2 + 2) + c * (a^2 + 2) * (b^2 + 2) - (a^2 + 2) * (b^2 + 2) * (c^2 + 2)) ) / ((a^2 + 2) * (b^2 + 2) * (c^2 + 2)) := by
      field_simp
      ring
    rw [h5]
    have h6 : (a * (b^2 + 2) * (c^2 + 2) + b * (a^2 + 2) * (c^2 + 2) + c * (a^2 + 2) * (b^2 + 2) - (a^2 + 2) * (b^2 + 2) * (c^2 + 2)) ≤ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc]
    have h7 : (a * (b^2 + 2) * (c^2 + 2) + b * (a^2 + 2) * (c^2 + 2) + c * (a^2 + 2) * (b^2 + 2) - (a^2 + 2) * (b^2 + 2) * (c^2 + 2)) / ((a^2 + 2) * (b^2 + 2) * (c^2 + 2)) ≤ 0 := by 
      apply div_nonpos_of_nonpos_of_nonneg
      linarith
      positivity
    linarith
  linarith