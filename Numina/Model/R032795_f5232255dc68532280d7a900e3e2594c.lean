import Mathlib

theorem inequalities_308235 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) + d / (d ^ 2 + 1) ≤ 16 / 17 := by
  have h1 : ∀ x : ℝ, 0 < x → x / (x ^ 2 + 1) ≤ 4 / 17 + (240 / 289) * (x - 1 / 4) := by
    intro x hx
    have h2 : x ^ 2 + 1 > 0 := by
      nlinarith
    apply (div_le_iff₀ h2).mpr
    nlinarith [sq_nonneg (x - 1 / 4), sq_nonneg (x - 4), sq_nonneg (x - 1 / 4), sq_nonneg (x + 1 / 4), sq_nonneg (x ^ 2 - 1 / 16), sq_nonneg (x - 1 / 2)]
  have h2 := h1 a ha
  have h3 := h1 b hb
  have h4 := h1 c hc
  have h5 := h1 d hd
  linarith [h2, h3, h4, h5, h]