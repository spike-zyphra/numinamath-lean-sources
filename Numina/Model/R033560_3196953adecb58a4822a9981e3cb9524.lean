import Mathlib

theorem inequalities_259302 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a + b ≤ 1) (h2 : a + c ≤ 1) (h3 : b + c ≤ 1) :
    a^2 + b^2 + c^2 ≤ a + b + c - a * b - b * c - c * a ∧
    a + b + c - a * b - b * c - c * a ≤ (1 + a^2 + b^2 + c^2) / 2 := by 
  constructor
  · -- Prove the first inequality
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  · -- Prove the second inequality
    nlinarith [sq_nonneg (a + b + c - 1)]