import Mathlib

theorem algebra_122638 (a b c d e f : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f)
    (h₁ : a * 1.2 = b)
    (h₂ : b * 9 = a * 15 + b * 12 + c * 6 + d * 3 + e * 2 + f * 1) :
    d * 60 = 45 := by
  rcases h₀ with ⟨ha, hb, hc, hd, he, hf⟩

  nlinarith [h₁, h₂, mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos ha he, mul_pos ha hf, mul_pos hb hc, mul_pos hb hd, mul_pos hb he, mul_pos hb hf, mul_pos hc hd, mul_pos hc he, mul_pos hc hf, mul_pos hd he, mul_pos hd hf, mul_pos he hf]