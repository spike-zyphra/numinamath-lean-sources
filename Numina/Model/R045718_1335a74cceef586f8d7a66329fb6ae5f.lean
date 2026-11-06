import Mathlib

open Real

theorem inequalities_6578 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * b * c * d = 1) :
    1 ≤ 1 / (a + 1)^2 + 1 / (b + 1)^2 + 1 / (c + 1)^2 + 1 / (d + 1)^2 := by

  have H1 : ∀ x y : ℝ, 0 < x → 0 < y → 1 / (x + 1) ^ 2 + 1 / (y + 1) ^ 2 ≥ 1 / (x * y + 1) := by
    intro x y hx hy
    have h1 : 0 < (x + 1) ^ 2 * (y + 1) ^ 2 * (x * y + 1) := by positivity
    have h2 : 1 / (x + 1) ^ 2 + 1 / (y + 1) ^ 2 - 1 / (x * y + 1) ≥ 0 := by
      have h3 : 1 / (x + 1) ^ 2 + 1 / (y + 1) ^ 2 - 1 / (x * y + 1) =
          ( (y + 1) ^ 2 * (x * y + 1) + (x + 1) ^ 2 * (x * y + 1) - (x + 1) ^ 2 * (y + 1) ^ 2 ) / ( (x + 1) ^ 2 * (y + 1) ^ 2 * (x * y + 1) ) := by
        field_simp
        ring
      rw [h3]
      have h4 : (y + 1) ^ 2 * (x * y + 1) + (x + 1) ^ 2 * (x * y + 1) - (x + 1) ^ 2 * (y + 1) ^ 2 ≥ 0 := by
        nlinarith [ sq_nonneg (x * y - 1), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y), 
                    mul_pos hx hy, sq_nonneg (x * y * x - x * y * y), sq_nonneg (x * y - 1) ]
      have h5 : ( (y + 1) ^ 2 * (x * y + 1) + (x + 1) ^ 2 * (x * y + 1) - (x + 1) ^ 2 * (y + 1) ^ 2 ) / ( (x + 1) ^ 2 * (y + 1) ^ 2 * (x * y + 1) ) ≥ 0 := by
        apply div_nonneg
        linarith
        positivity
      linarith
    linarith

  have h1 := H1 a c ha hc
  have h2 := H1 b d hb hd
  have h3 : 1 / (a + 1) ^ 2 + 1 / (c + 1) ^ 2 ≥ 1 / (a * c + 1) := by linarith
  have h4 : 1 / (b + 1) ^ 2 + 1 / (d + 1) ^ 2 ≥ 1 / (b * d + 1) := by linarith
  have h5 : a * c > 0 := mul_pos ha hc
  have h6 : b * d > 0 := mul_pos hb hd
  have h7 : (a * c) * (b * d) = 1 := by
    calc
      (a * c) * (b * d) = a * b * c * d := by ring
      _ = 1 := h

  have h8 : 1 / (a * c + 1) + 1 / (b * d + 1) ≥ 1 := by
    have h9 : (b * d) = 1 / (a * c) := by
      have h13 : (a * c) * (b * d) = 1 := h7
      field_simp [(show a * c ≠ 0 by positivity)]
      all_goals nlinarith
    rw [h9]
    have h11 : a * c > 0 := by positivity
    have h12 : 1 / (a * c + 1) + 1 / ((1 / (a * c)) + 1) = 1 := by
      field_simp
      all_goals nlinarith
    nlinarith [ h12 ]

  linarith [ h1, h2, h8 ]