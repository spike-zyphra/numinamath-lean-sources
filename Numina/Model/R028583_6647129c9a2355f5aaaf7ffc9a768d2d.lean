import Mathlib

theorem inequalities_604085
    (a b c d : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (hd : 0 ≤ d)
    (h : a + b + c + d = 4) :
    a^2 + b^2 + c^2 + d^2 - 4 ≥ 4 * (a - 1) * (b - 1) * (c - 1) * (d - 1) := by
  have h1 : d = 4 - a - b - c := by linarith
  rw [h1] at *
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - (4 - a - b - c : ℝ)), 
          sq_nonneg (b - c), sq_nonneg (b - (4 - a - b - c : ℝ)), 
          sq_nonneg (c - (4 - a - b - c : ℝ)), 
          mul_nonneg ha hb, 
          mul_nonneg ha hc, 
          mul_nonneg ha (show 0 ≤ (4 - a - b - c : ℝ) by nlinarith), 
          mul_nonneg hb hc, 
          mul_nonneg hb (show 0 ≤ (4 - a - b - c : ℝ) by nlinarith), 
          mul_nonneg (show 0 ≤ (4 - a - b - c : ℝ) by nlinarith) hc, 
          sq_nonneg ((a - 1) + (b - 1)), sq_nonneg ((a - 1) + (c - 1)), sq_nonneg ((a - 1) + ((4 - a - b - c : ℝ) - 1)), 
          sq_nonneg ((b - 1) + (c - 1)), sq_nonneg ((b - 1) + ((4 - a - b - c : ℝ) - 1)), 
          sq_nonneg ((c - 1) + ((4 - a - b - c : ℝ) - 1))
          ]