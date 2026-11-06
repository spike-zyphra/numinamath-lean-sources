import Mathlib

open Real

theorem inequalities_91984 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a^2 ≤ b^2 + c^2) (h2 : b^2 ≤ c^2 + a^2) (h3 : c^2 ≤ a^2 + b^2) :
    (a + b + c) * (a^2 + b^2 + c^2) * (a^3 + b^3 + c^3) ≥ 4 * (a^6 + b^6 + c^6) := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc, 
          mul_nonneg (show 0 ≤ b ^ 2 + c ^ 2 - a ^ 2 by nlinarith) (show 0 ≤ c ^ 2 + a ^ 2 - b ^ 2 by nlinarith), 
          mul_nonneg (show 0 ≤ c ^ 2 + a ^ 2 - b ^ 2 by nlinarith) (show 0 ≤ a ^ 2 + b ^ 2 - c ^ 2 by nlinarith), 
          mul_nonneg (show 0 ≤ b ^ 2 + c ^ 2 - a ^ 2 by nlinarith) (show 0 ≤ a ^ 2 + b ^ 2 - c ^ 2 by nlinarith)]