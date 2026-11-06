import Mathlib

theorem inequalities_602966 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hord : a ≥ b ∧ b ≥ c) :
    a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) ≥ 0 := by
  have h1 : a ≥ b := hord.1
  have h2 : b ≥ c := hord.2
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)),
          mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ b - c by linarith),
          mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ c by linarith),
          mul_nonneg (show 0 ≤ b - c by linarith) (show 0 ≤ c by linarith),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
]