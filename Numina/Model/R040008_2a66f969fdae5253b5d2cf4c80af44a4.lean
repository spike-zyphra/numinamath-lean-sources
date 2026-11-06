import Mathlib

theorem inequalities_295992 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c = 3) :
    3 / 2 ≤ a / (b ^ 2 + 1) + b / (c ^ 2 + 1) + c / (a ^ 2 + 1) := by

  have h1 : ∀ x y : ℝ, 0 < x → 0 < y → x / (y ^ 2 + 1) ≥ x - x * y / 2 := by
    intro x y hx hy
    have h2 : 0 < y ^ 2 + 1 := by nlinarith
    apply (le_div_iff₀ (by positivity)).mpr
    have h3 : x * y * (y - 1) ^ 2 ≥ 0 := by
      positivity
    nlinarith [sq_nonneg (y - 1)]
  
  have h2 : a / (b ^ 2 + 1) ≥ a - a * b / 2 := h1 a b ha hb
  have h3 : b / (c ^ 2 + 1) ≥ b - b * c / 2 := h1 b c hb hc
  have h4 : c / (a ^ 2 + 1) ≥ c - c * a / 2 := h1 c a hc ha

  have h5 : a / (b ^ 2 + 1) + b / (c ^ 2 + 1) + c / (a ^ 2 + 1) ≥ (a - a * b / 2) + (b - b * c / 2) + (c - c * a / 2) := by
    linarith [h2, h3, h4]

  have h6 : (a - a * b / 2) + (b - b * c / 2) + (c - c * a / 2) = 3 - (a * b + b * c + c * a) / 2 := by
    nlinarith [hsum]

  have h7 : 3 - (a * b + b * c + c * a) / 2 ≥ 3 / 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      hsum, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  linarith [h5, h6, h7]