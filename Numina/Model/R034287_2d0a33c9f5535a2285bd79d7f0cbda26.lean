import Mathlib

theorem inequalities_87454 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a / (b + c + 1) + b / (c + a + 1) + c / (a + b + 1) ≤ 1) :
    1 ≤ 1 / (b + c + 1) + 1 / (c + a + 1) + 1 / (a + b + 1) := by

  have h1 : 0 < (b + c + 1) * (c + a + 1) * (a + b + 1) := by
    positivity

  have h2 : a * (c + a + 1) * (a + b + 1) + b * (b + c + 1) * (a + b + 1) + c * (b + c + 1) * (c + a + 1) ≤ (b + c + 1) * (c + a + 1) * (a + b + 1) := by
    have h3 : a / (b + c + 1) + b / (c + a + 1) + c / (a + b + 1) - 1 ≤ 0 := by linarith
    have h4 : (a / (b + c + 1) + b / (c + a + 1) + c / (a + b + 1) - 1) = ( (a * (c + a + 1) * (a + b + 1) + b * (b + c + 1) * (a + b + 1) + c * (b + c + 1) * (c + a + 1) - (b + c + 1) * (c + a + 1) * (a + b + 1)) / ((b + c + 1) * (c + a + 1) * (a + b + 1)) ) := by
      field_simp
      ring
    rw [h4] at h3
    apply (div_nonpos_iff).mp at h3
    cases h3 with
    | inl h5 =>
      nlinarith
    | inr h6 =>
      nlinarith [show 0 < (b + c + 1) * (c + a + 1) * (a + b + 1) by positivity]

  have h3 : 1 ≤ 1 / (b + c + 1) + 1 / (c + a + 1) + 1 / (a + b + 1) := by
    have h4 : (1 / (b + c + 1) + 1 / (c + a + 1) + 1 / (a + b + 1) - 1) ≥ 0 := by
      have h5 : (1 / (b + c + 1) + 1 / (c + a + 1) + 1 / (a + b + 1) - 1) =
          ( (c + a + 1) * (a + b + 1) + (b + c + 1) * (a + b + 1) + (b + c + 1) * (c + a + 1) - (b + c + 1) * (c + a + 1) * (a + b + 1)) / ((b + c + 1) * (c + a + 1) * (a + b + 1)) := by
        field_simp
        ring
      rw [h5]
      have h6 : (c + a + 1) * (a + b + 1) + (b + c + 1) * (a + b + 1) + (b + c + 1) * (c + a + 1) - (b + c + 1) * (c + a + 1) * (a + b + 1) ≥ 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc,
          mul_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)]
      have hn7 : ( (c + a + 1) * (a + b + 1) + (b + c + 1) * (a + b + 1) + (b + c + 1) * (c + a + 1) - (b + c + 1) * (c + a + 1) * (a + b + 1)) / ((b + c + 1) * (c + a + 1) * (a + b + 1)) ≥ 0 := by
        apply div_nonneg
        linarith
        positivity
      linarith
    linarith

  exact h3