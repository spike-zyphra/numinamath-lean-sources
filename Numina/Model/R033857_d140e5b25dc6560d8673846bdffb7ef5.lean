import Mathlib

open Real

  theorem Inequalities_605591 (a b c : ℝ) (h : 0 < a ∧ 0 < b ∧ 0 < c) (h_prod : a * b * c = 1 / 8) :
    a^2 + b^2 + c^2 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≥ 15 / 16 
     := by
  rcases h with ⟨ha, hb, hc⟩
  nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2), 
          sq_nonneg (a * b - 1 / 4), sq_nonneg (a * c - 1 / 4), sq_nonneg (b * c - 1 / 4), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
]