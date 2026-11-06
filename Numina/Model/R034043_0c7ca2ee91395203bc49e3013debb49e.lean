import Mathlib

theorem inequalities_598968
    (a b c d : ℝ)
    (A B : ℝ)
    (h₀ : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d)
    (h₁ : A = a^3 + b^3 + c^3 + d^3)
    (h₂ : B = b * c * d + c * d * a + d * a * b + a * b * c) :
    (a + b + c + d)^3 ≤ 4 * A + 24 * B := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  rw [h₁, h₂]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
          sq_nonneg (a + b + c - d), sq_nonneg (a + b + d - c), sq_nonneg (a + c + d - b), sq_nonneg (b + c + d - a),
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc hd, mul_nonneg ha hc, mul_nonneg ha hd, mul_nonneg hb hd,
          mul_nonneg (mul_nonneg ha hb) hc, mul_nonneg (mul_nonneg ha hb) hd, mul_nonneg (mul_nonneg ha hc) hd, mul_nonneg (mul_nonneg hb hc) hd
]