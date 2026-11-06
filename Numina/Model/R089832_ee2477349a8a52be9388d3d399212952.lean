import Mathlib

open Real

theorem inequalities_243514 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (f : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hf : f = fun a b c d => a / (b + c + d) + b / (c + d + a) + c / (a + b + d) +
      d / (a + b + c)) :
    f a b c d ≥ 4 / 3 := by
  rw [hf]
  have h₁ : a / (b + c + d) + b / (c + d + a) + c / (a + b + d) + d / (a + b + c) - 4 / 3 ≥ 0 := by
    have h₁ : 0 < a + b + c + d := by positivity
    have h₂ : 0 < b + c + d := by linarith [ha, hb, hc, hd]
    have h₃ : 0 < c + d + a := by linarith [ha, hb, hc, hd]
    have h₄ : 0 < a + b + d := by linarith [ha, hb, hc, hd];
    have h₅ : 0 < a + b + c := by linarith [ha, hb, hc, hd];
    have h₆ : a / (b + c + d) + b / (c + d + a) + c / (a + b + d) + d / (a + b + c) - 4 / 3 =
      (a * (c + d + a) * (a + b + d) * (a + b + c) +
        b * (b + c + d) * (a + b + d) * (a + b + c) +
        c * (b + c + d) * (c + d + a) * (a + b + c) +
        d * (b + c + d) * (c + d + a) * (a + b + d) - (4 / 3) * (b + c + d) * (c + d + a) * (a + b + d) * (a + b + c))
        / ((b + c + d) * (c + d + a) * (a + b + d) * (a + b + c)) := by
      field_simp
      ring
    rw [h₆]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
      sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
      mul_pos ha hb, mul_pos ha hc, mul_pos ha hd,
      mul_pos hb hc, mul_pos hb hd,
      mul_pos hc hd
    ]
    all_goals positivity
  linarith
  all_goals norm_num