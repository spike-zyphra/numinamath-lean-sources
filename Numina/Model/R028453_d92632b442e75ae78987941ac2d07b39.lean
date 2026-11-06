import Mathlib

theorem inequalities_63247 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = a * b * c) :
    17 / 10 < a ∨ 17 / 10 < b ∨ 17 / 10 < c := by
  by_contra h1 
  push_neg at h1 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_nonneg (show 0 ≤ 17 / 10 - a by linarith [h1.1]) 
                      (show 0 ≤ 17 / 10 - b by linarith [h1.2.1]), 
          mul_nonneg (show 0 ≤ 17 / 10 - a by linarith [h1.1]) 
                      (show 0 ≤ 17 / 10 - c by linarith [h1.2.2]), 
          mul_nonneg (show 0 ≤ 17 / 10 - b by linarith [h1.2.1]) 
                      (show 0 ≤ 17 / 10 - c by linarith [h1.2.2])
        ]