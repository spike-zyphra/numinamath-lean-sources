import Mathlib

theorem inequalities_265103 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a * b + b * c + c * a = 1 / 3) :
    1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) +
    1 / (c ^ 2 - a * b + 1) ≤ 3 := by
  have h1 : 0 < a ^ 2 - b * c + 1 := by nlinarith
  have h2 : 0 < b ^ 2 - c * a + 1 := by nlinarith
  have h3 : 0 < c ^ 2 - a * b + 1 := by nlinarith
  have h4 : 1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) + 1 / (c ^ 2 - a * b + 1) - 3 ≤ 0 := by
    have h5 : (1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) + 1 / (c ^ 2 - a * b + 1) - 3) = 
      ( (b ^ 2 - c * a + 1) * (c ^ 2 - a * b + 1) + (a ^ 2 - b * c + 1) * (c ^ 2 - a * b + 1) + (a ^ 2 - b * c + 1) * (b ^ 2 - c * a + 1) - 3 * (a ^ 2 - b * c + 1) * (b ^ 2 - c * a + 1) * (c ^ 2 - a * b + 1) ) / ( (a ^ 2 - b * c + 1) * (b ^ 2 - c * a + 1) * (c ^ 2 - a * b + 1) ) := by
      field_simp
      <;> ring
    rw [h5]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is ≤ 0
      nlinarith [ sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * b + b * c + c * a - 1 / 3), 
          sq_nonneg (a * (b - c) + b * (c - a) + c * (a - b)), 
          sq_nonneg ( (a * b - b * c) + (b * c - c * a) + (c * a - a * b) ), 
          mul_nonneg ha hb, 
          mul_nonneg hb hc, 
          mul_nonneg ha hc, 
          mul_nonneg (show 0 ≤ a * b by nlinarith) (show 0 ≤ b * c by nlinarith ), 
          mul_nonneg (show 0 ≤ a * b by nlinarith ) (show 0 ≤ c * a by nlinarith ), 
          mul_nonneg (show 0 ≤ b * c by nlinarith ) (show 0 ≤ c * a by nlinarith )
          ]
    · -- Show that the denominator is ≥ 0
      positivity
  linarith