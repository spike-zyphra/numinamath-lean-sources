import Mathlib

theorem inequalities_603332
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) ∧
    a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) ≥
    (a + b + c) / 2 := by

  constructor
  · -- Proof of first inequality
    have h1 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
      have h11 : 0 < (b + c) * (c + a) * (a + b) := by
        positivity
      have h12 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
        (2 * (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a)) - 3 * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) := by
        field_simp
        ring
      rw [h12]
      have hn : 2 * (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a)) - 3 * (b + c) * (c + a) * (a + b) ≥ 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]
      apply div_nonneg
      linarith
      positivity
    linarith
  · -- Proof of the second inequality
    have h2 : a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) - (a + b + c) / 2 ≥ 0 := by
      have h21 : 0 < (b + c) * (c + a) * (a + b) := by
        positivity
      have h22 : a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) - (a + b + c) / 2 =
        (2 * (a ^ 2 * (c + a) * (a + b) + b ^ 2 * (b + c) * (a + b) + c ^ 2 * (b + c) * (c + a)) - (a + b + c) * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) := by
        field_simp
        ring
      rw [h22]
      have hn : 2 * (a ^ 2 * (c + a) * (a + b) + b ^ 2 * (b + c) * (a + b) + c ^ 2 * (b + c) * (c + a)) - (a + b + c) * (b + c) * (c + a) * (a + b) ≥ 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]
      apply div_nonneg
      linarith
      positivity
    linarith