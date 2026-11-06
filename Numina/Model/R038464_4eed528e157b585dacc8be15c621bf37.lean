import Mathlib

theorem inequalities_210991
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hord : a ≥ b ∧ b ≥ c)
    (hsum : a + b + c ≤ 1) :
    a^2 + 3 * b^2 + 5 * c^2 ≤ 1 := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          mul_nonneg (show 0 ≤ a - b by linarith [hord.1]) (show 0 ≤ b - c by linarith [hord.2]), 
          mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ b - c by linarith [hord.2]), 
          sq_nonneg (a + b + c - 1), mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ b by linarith), 
          mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ a by linarith), 
          mul_nonneg (show 0 ≤ a - b by linarith [hord.1]) (show 0 ≤ c by linarith) 
        ]