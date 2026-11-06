import Mathlib

theorem inequalities_270617
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a + b + c = 1) :
    0 ≤ a * (3 * a - 1) / (1 + a ^ 2) + b * (3 * b - 1) / (1 + b ^ 2) +
        c * (3 * c - 1) / (1 + c ^ 2) := by 
  have hc1 : c = 1 - a - b := by linarith 
  rw [hc1]
  have ha1 : 0 < a := ha 
  have hb1 : 0 < b := hb
  have hc2 : 0 < 1 - a - b := by nlinarith 
  have h1 : a * (3 * a - 1) / (1 + a ^ 2) + b * (3 * b - 1) / (1 + b ^ 2) + (1 - a - b) * (3 * (1 - a - b) - 1) / (1 + (1 - a - b) ^ 2) ≥ 0 := by
    have h4 : a * (3 * a - 1) / (1 + a ^ 2) + b * (3 * b - 1) / (1 + b ^ 2) + (1 - a - b) * (3 * (1 - a - b) - 1) / (1 + (1 - a - b) ^ 2) = 
        (a * (3 * a - 1) * (1 + b ^ 2) * (1 + (1 - a - b) ^ 2) + b * (3 * b - 1) * (1 + a ^ 2) * (1 + (1 - a - b) ^ 2) + (1 - a - b) * (3 * (1 - a - b) - 1) * (1 + a ^ 2) * (1 + b ^ 2)) / ((1 + a ^ 2) * (1 + b ^ 2) * (1 + (1 - a - b) ^ 2)) := by 
      field_simp 
      <;> ring
    rw [h4] 
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg ((1 - a - b) - 1 / 3), 
          mul_pos ha hb, mul_pos ha hc2, mul_pos hb hc2, 
          sq_nonneg (a * b - b * (1 - a - b)), sq_nonneg (b * (1 - a - b) - a * (1 - a - b)), sq_nonneg (a * b - a * (1 - a - b))
    ]
    positivity
  linarith