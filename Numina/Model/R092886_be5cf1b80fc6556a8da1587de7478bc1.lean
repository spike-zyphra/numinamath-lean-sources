import Mathlib

theorem inequalities_236136 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hle : a ≤ b ∧ b ≤ c ∧ c ≤ d) (hsum : 1 ≤ a + b + c + d) :
    a^2 + 3 * b^2 + 5 * c^2 + 7 * d^2 ≥ 1 := by 
  rcases hle with ⟨h1, h2, h3⟩
  nlinarith [sq_nonneg (a - 1 / 4), sq_nonneg (b - 1 / 4), sq_nonneg (c - 1 / 4), sq_nonneg (d - 1 / 4),
    hsum, mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b - a by linarith [h1, hb]), mul_nonneg (show 0 ≤ b by linarith [hb] ) (show 0 ≤ c - b by linarith [h2, hc] ), 
          mul_nonneg (show 0 ≤ c by linarith [hc] ) (show 0 ≤ d - c by linarith [h3, hd] ) 
          ]