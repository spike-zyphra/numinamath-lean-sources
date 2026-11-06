import Mathlib

theorem inequalities_139726 (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    a^5 + b^3 + (a - b)^2 ≤ 2 := by
  have h1 : 0 ≤ a := ha.1
  have h2 : a ≤ 1 := ha.2
  have h3 : 0 ≤ b := hb.1
  have h4 : b ≤ 1 := hb.2
  
  nlinarith [sq_nonneg (a - a ^ 2), sq_nonneg (b - b ^ 2), 
          sq_nonneg (a - b), 
          sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), 
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ 1 - a by linarith),
          mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ 1 - b by linarith),
          sq_nonneg (a ^ 2 - a), sq_nonneg (b ^ 2 - b),
          sq_nonneg (a * b - a * b), 
          sq_nonneg (a ^ 2 - b ^ 2)]