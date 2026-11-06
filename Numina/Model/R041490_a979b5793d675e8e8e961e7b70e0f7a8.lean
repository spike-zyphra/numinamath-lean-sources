import Mathlib

theorem inequalities_600543 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 1) :
    2 * (a^2 + b^2 + c^2) + 9 * a * b * c ≥ 1 := by 
  have hc2 : c = 1 - a - b := by linarith 
  rw [hc2]
  have h1 : 0 ≤ a := by linarith
  have h2 : 0 ≤ b := by linarith
  have h3 : 0 ≤ (1 - a - b) := by nlinarith 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
      mul_nonneg ha hb, 
      mul_nonneg ha (show 0 ≤ 1 - a - b by nlinarith), 
      mul_nonneg hb (show 0 ≤ 1 - a - b by nlinarith), 
      sq_nonneg (a + b - (1 - a - b)), 
      mul_nonneg (show 0 ≤ a * b by nlinarith) (show 0 ≤ (1 - a - b) by nlinarith)
    ]