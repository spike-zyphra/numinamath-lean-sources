import Mathlib


theorem inequalities_109998 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
  (hc : 0 < c) (h : a + b > c) (_ : a + c > b) (_ : b + c > a) :
    a^3 / c^3 + b^3 / c^3 + 3 * a * b / c^2 > 1 := by
  have hc3_pos : 0 < c^3 := by positivity
  have h1 : a ^ 3 / c ^ 3 + b ^ 3 / c ^ 3 + 3 * a * b / c ^ 2 - 1 > 0 := by
    have h2 : a ^ 3 + b ^ 3 + 3 * a * b * c > c ^ 3 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_pos (sub_pos.mpr h) (sub_pos.mpr h), 
          mul_pos (sub_pos.mpr (show a + c - b > 0 by linarith)) (sub_pos.mpr (show b + c - a > 0 by linarith)), 
            sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)
        ]
    have h3 : a ^ 3 / c ^ 3 + b ^ 3 / c ^ 3 + 3 * a * b / c ^ 2 - 1 = (a ^ 3 + b ^ 3 + 3 * a * b * c - c ^ 3) / c ^ 3 := by
      field_simp
      ring
    rw [h3]
    apply div_pos
    linarith
    positivity
  linarith