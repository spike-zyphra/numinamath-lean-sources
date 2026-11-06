import Mathlib

theorem inequalities_309212
    (a b c : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (hsum : a + b + c = 1) :
    9 * a * b * c ≤ a * b + b * c + c * a ∧
    a * b + b * c + c * a ≤ (1 / 4) * (1 + 9 * a * b * c) := by 
  have h1 : 9 * a * b * c ≤ a * b + b * c + c * a := by
    have hc1 : c = 1 - a - b := by linarith
    rw [hc1]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          mul_nonneg ha hb, 
          mul_nonneg hb (show 0 ≤ 1 - a - b by nlinarith), 
          mul_nonneg ha (show 0 ≤ 1 - a - b by nlinarith), 
          sq_nonneg (a + b - 2 / 9), 
          sq_nonneg (a - 2 / 9), 
          sq_nonneg (b - 2 / 9), 
          sq_nonneg ((1 - a - b) - 5 / 9)]
  have h2 : a * b + b * c + c * a ≤ (1 / 4) * (1 + 9 * a * b * c) := by 
    have hc1 : c = 1 - a - b := by linarith
    rw [hc1]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          mul_nonneg ha hb, 
          mul_nonneg hb (show 0 ≤ 1 - a - b by nlinarith), 
          mul_nonneg ha (show 0 ≤ 1 - a - b by nlinarith), 
          sq_nonneg (a + b - 1 / 2), 
          sq_nonneg (a - 1 / 2), 
          sq_nonneg (b - 1 / 2), 
          sq_nonneg ((1 - a - b) - 1 / 2)]
  constructor
  · exact h1
  · exact h2