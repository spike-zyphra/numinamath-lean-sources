import Mathlib

open Real

theorem inequalities_77460 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a + 1 / b) ^ 2 + (b + 1 / c) ^ 2 + (c + 1 / a) ^ 2 ≥ 3 * (a + b + c + 1) := by
  have h3 : (a + 1 / b) ^ 2 + (b + 1 / c) ^ 2 + (c + 1 / a) ^ 2 - 3 * (a + b + c + 1) ≥ 0 := by
    have pos1 : 0 < a * b * c := by positivity
    have h4 : (a + 1 / b) ^ 2 + (b + 1 / c) ^ 2 + (c + 1 / a) ^ 2 - 3 * (a + b + c + 1) =
          ( (a^2 + 2 * a / b + 1 / b^2) + (b^2 + 2 * b / c + 1 / c^2) + (c^2 + 2 * c / a + 1 / a^2) - 3 * (a + b + c + 1) ) := by
      field_simp
      <;> ring
    rw [h4]
    have h5 : (a^2 + 2 * a / b + 1 / b^2) + (b^2 + 2 * b / c + 1 / c^2) + (c^2 + 2 * c / a + 1 / a^2) - 3 * (a + b + c + 1) ≥ 0 := by
      have pos2 : 0 < a ^ 2 * b ^ 2 * c ^ 2 := by positivity
      have h6 : (a^2 + 2 * a / b + 1 / b^2) + (b^2 + 2 * b / c + 1 / c^2) + (c^2 + 2 * c / a + 1 / a^2) - 3 * (a + b + c + 1) =
            ( (a^4 * b^2 * c^2 + 2 * a^3 * b * c^2 + a^2 * c^2) + (a^2 * b^4 * c^2 + 2 * a^2 * b^3 * c + a^2 * b^2) + (a^2 * b^2 * c^4 + 2 * a * b^2 * c^3 + b^2 * c^2) - 3 * (a^3 * b^2 * c^2 + a^2 * b^3 * c^2 + a^2 * b^2 * c^3 + a^2 * b^2 * c^2) ) / (a^2 * b^2 * c^2) := by
        field_simp
        ring
      rw [h6]
      have pos3 : 0 < a^2 * b^2 * c^2 := by positivity
      have h7 : (a^4 * b^2 * c^2 + 2 * a^3 * b * c^2 + a^2 * c^2) + (a^2 * b^4 * c^2 + 2 * a^2 * b^3 * c + a^2 * b^2) + (a^2 * b^2 * c^4 + 2 * a * b^2 * c^3 + b^2 * c^2) - 3 * (a^3 * b^2 * c^2 + a^2 * b^3 * c^2 + a^2 * b^2 * c^3 + a^2 * b^2 * c^2) ≥ 0 := by
        have h8 : a * b * c = 1 := habc
        have h9 : a^4 * b^2 * c^2 = a^2 := by
          calc
            a^4 * b^2 * c^2 = (a^2 * (a * b * c)^2) := by ring
            _ = (a^2 * (1)^2) := by rw [habc]
            _ = a^2 := by ring
        have h10 : a^2 * b^4 * c^2 = b^2 := by
          calc
            a^2 * b^4 * c^2 = (b^2 * (a * b * c)^2) := by ring
            _ = (b^2 * (1)^2) := by rw [habc]
            _ = b^2 := by ring
        have h11 : a^2 * b^2 * c^4 = c^2 := by
          calc
            a^2 * b^2 * c^4 = (c^2 * (a * b * c)^2) := by ring
            _ = (c^2 * (1)^2) := by rw [habc]
            _ = c^2 := by ring
        have h12 : a^3 * b^2 * c^2 = a := by
          calc
            a^3 * b^2 * c^2 = a * (a * b * c)^2 := by ring
            _ = a * (1)^2 := by rw [habc]
            _ = a := by ring
        have h13 : a^2 * b^3 * c^2 = b := by
          calc
            a^2 * b^3 * c^2 = b * (a * b * c)^2 := by ring
            _ = b * (1)^2 := by rw [habc]
            _ = b := by ring
        have h14 : a^2 * b^2 * c^3 = c := by
          calc
            a^2 * b^2 * c^3 = c * (a * b * c)^2 := by ring
            _ = c * (1)^2 := by rw [habc]
            _ = c := by ring
        have h15 : a^2 * b^2 * c^2 = 1 := by
          calc
            a^2 * b^2 * c^2 = (a * b * c)^2 := by ring
            _ = (1)^2 := by rw [habc]
            _ = (1 : ℝ) := by norm_num
        rw [h9, h10, h11, h12, h13, h14, h15]
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          mul_pos (mul_pos ha hb) hc
        ]
      apply div_nonneg
      linarith
      all_goals positivity
    linarith
  linarith