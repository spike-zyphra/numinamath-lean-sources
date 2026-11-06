import Mathlib

theorem inequalities_70692 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a / (a ^ 2 + 2) + b / (b ^ 2 + 2) + c / (c ^ 2 + 2) ≤ 1 := by 
  have h : a / (a ^ 2 + 2) + b / (b ^ 2 + 2) + c / (c ^ 2 + 2) - 1 ≤ 0 := by
    have h1 : a * b * c = 1 := habc
    have h2 : a / (a ^ 2 + 2) + b / (b ^ 2 + 2) + c / (c ^ 2 + 2) - 1 =
        ( a * (b^2 + 2) * (c^2 + 2) + b * (a^2 + 2) * (c^2 + 2) + c * (a^2 + 2) * (b^2 + 2) - (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ) / ((a^2 + 2) * (b^2 + 2) * (c^2 + 2)) := by
      field_simp
      ring
    have h3 : a * (b^2 + 2) * (c^2 + 2) + b * (a^2 + 2) * (c^2 + 2) + c * (a^2 + 2) * (b^2 + 2) - (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ≤ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, habc]
    have h4 : a * (b^2 + 2) * (c^2 + 2) + b * (a^2 + 2) * (c^2 + 2) + c * (a^2 + 2) * (b^2 + 2) - (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ≤ 0 := h3
    have h5 : a / (a ^ 2 + 2) + b / (b ^ 2 + 2) + c / (c ^ 2 + 2) - 1 =
        ( a * (b^2 + 2) * (c^2 + 2) + b * (a^2 + 2) * (c^2 + 2) + c * (a^2 + 2) * (b^2 + 2) - (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ) / ((a^2 + 2) * (b^2 + 2) * (c^2 + 2)) := h2
    rw [h5]
    apply div_nonpos_of_nonpos_of_nonneg
    linarith [h3]
    positivity
  linarith