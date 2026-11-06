import Mathlib

theorem inequalities_598852
    (a b c : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (h1 : b + c ≤ 1 + a)
    (h2 : a + c ≤ 1 + b)
    (h3 : a + b ≤ 1 + c) :
    a^2 + b^2 + c^2 ≤ 2 * a * b * c + 1 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc, 
          mul_nonneg (show 0 ≤ 1 + a - b - c by linarith) 
                      (show 0 ≤ 1 + b - a - c by linarith), 
          mul_nonneg (show 0 ≤ 1 + b - a - c by linarith) 
                      (show 0 ≤ 1 + c - a - b by linarith), 
          mul_nonneg (show 0 ≤ 1 + a - b - c by linarith) 
                      (show 0 ≤ 1 + c - a - b by linarith) 
        ]