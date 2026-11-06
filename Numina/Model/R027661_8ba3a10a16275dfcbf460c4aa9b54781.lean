import Mathlib

open Real Set

theorem algebra_286579 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + 4 * b^2 + 9 * c^2 = 4 * b + 12 * c - 2) :
    6 ≤ 1 / a + 2 / b + 3 / c := by
  have h1 : 0 < a * b * c := by
    positivity 
  suffices 6 ≤ 1 / a + 2 / b + 3 / c  by 
    linarith 
  have h3 : 1 / a + 2 / b + 3 / c - 6 ≥ 0 := by 
    have h4 : 0 < a * b * c := h1
    have h5 : (1 / a + 2 / b + 3 / c - 6) = (b * c + 2 * a * c + 3 * a * b - 6 * a * b * c) / (a * b * c) := by 
      field_simp 
      ring
    rw [h5] 
    apply div_nonneg 
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          sq_nonneg (a * (b - 1)), sq_nonneg (b * (a - 1)), 
          sq_nonneg (c * (a - 1)), sq_nonneg (c * (b - 1)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          h
        ]
    positivity 
  linarith