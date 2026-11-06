import Mathlib

theorem inequalities_599602 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) + 1 / (c ^ 2 + 1) = 2) :
    a * b + b * c + c * a ≤ 3 / 2 := by
  have h6 : a ^ 2 + 1 > 0 := by nlinarith
  have h7 : b ^ 2 + 1 > 0 := by nlinarith
  have h8 : c ^ 2 + 1 > 0 := by nlinarith
  have eq1 : (b^2 + 1) * (c^2 + 1) + (a^2 + 1) * (c^2 + 1) + (a^2 + 1) * (b^2 + 1) = 2 * (a^2 + 1) * (b^2 + 1) * (c^2 + 1) := by
    field_simp [(show a^2 + 1 ≠ 0 by nlinarith), (show b^2 + 1 ≠ 0 by nlinarith), (show c^2 + 1 ≠ 0 by nlinarith)] at h ⊢
    <;> nlinarith
  nlinarith [sq_nonneg (a * b - 1 / 2), sq_nonneg (b * c - 1 / 2), sq_nonneg (c * a - 1 / 2), 
          sq_nonneg (a * b + b * c + c * a - 3 / 2), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < c * a by nlinarith), 
          mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith) 
        ]