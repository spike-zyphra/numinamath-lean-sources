import Mathlib

theorem inequalities_50802 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (p q r : ℝ) (hp : p ∈ Set.Icc 0 (1 / 2)) (hq : q ∈ Set.Icc 0 (1 / 2)) (hr : r ∈ Set.Icc 0 (1 / 2))
    (h : p + q + r = 1) :
    p * a * b + q * b * c + r * c * a ≤ (1 / 8) * (a + b + c) ^ 2 := by
  rcases hp with ⟨hp0, hhp⟩
  rcases hq with ⟨hq0, hhq⟩
  rcases hr with ⟨hr0, hhr⟩
  have hp1 : p ≥ 0 := hp0
  have hp2 : p ≤ 1 / 2 := hhp
  have hq1 : q ≥ 0 := hq0
  have hq2 : q ≤ 1 / 2 := hhq
  have hr1 : r ≥ 0 := hr0
  have hr2 : r ≤ 1 / 2 := hhr
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b + c - 2 * a), sq_nonneg (a + b + c - 2 * b), sq_nonneg (a + b + c - 2 * c),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]