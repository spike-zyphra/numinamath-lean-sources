import Mathlib

theorem algebra_287878 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
    ∀ x : ℝ, b^2 * x^2 + (b^2 + c^2 - a^2) * x + c^2 > 0 := by
  intro x
  have h1 : 0 < b^2 := by
    nlinarith
  have h2 : b ^ 2 * x ^ 2 + (b ^ 2 + c ^ 2 - a ^ 2) * x + c ^ 2 > 0 := by
    nlinarith [sq_nonneg (b^2 * x + (b^2 + c^2 - a^2) / 2), sq_nonneg (c + a - b), sq_nonneg (c + b - a), sq_nonneg (b + a - c),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
              mul_pos (sub_pos_of_lt h) (sub_pos_of_lt h'), -- (a + b - c) * (a + c - b) > 0
              mul_pos (sub_pos_of_lt h) (sub_pos_of_lt h''), -- (a + b - c) * (b + c - a) > 0
              mul_pos (sub_pos_of_lt h') (sub_pos_of_lt h'') -- (a + c - b) * (b + c - a) > 0
              ]
  simpa using h2