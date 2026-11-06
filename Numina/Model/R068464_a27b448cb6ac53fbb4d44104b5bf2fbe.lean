import Mathlib

theorem inequalities_599604 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a * b / (a^5 + b^5 + a * b) + b * c / (b^5 + c^5 + b * c) +
    c * a / (c^5 + a^5 + c * a) ≤ 1 := by

  have h1 : ∀ x y : ℝ, x > 0 → y > 0 → x * y / (x^5 + y^5 + x * y) ≤ (1 / (x * y * (x + y) + 1)) := by
    intro x y hx hy
    have h1 : x^5 + y^5 ≥ x^2 * y^2 * (x + y) := by
      suffices x^5 + y^5 - x^2 * y^2 * (x + y) ≥ 0 by linarith
      nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x * y - y * x), sq_nonneg (x * y), sq_nonneg (x + y), sq_nonneg (x - y), mul_pos hx hy, mul_pos hx (show 0 < y by linarith), mul_pos (show 0 < x by linarith) hy
      ]
    have h3 : x * y / (x^5 + y^5 + x * y) ≤ (1 / (x * y * (x + y) + 1)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [h1]
    exact h3
  have h2 : a * b / (a^5 + b^5 + a * b) ≤ 1 / (a * b * (a + b) + 1) := h1 a b ha hb
  have h3 : b * c / (b^5 + c^5 + b * c) ≤ 1 / (b * c * (b + c) + 1) := h1 b c hb hc
  have h4 : c * a / (c^5 + a^5 + c * a) ≤ 1 / (c * a * (c + a) + 1) := h1 c a hc ha

  have h5 : 1 / (a * b * (a + b) + 1) = c / (a + b + c) := by
    field_simp
    nlinarith [habc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h6 : 1 / (b * c * (b + c) + 1) = a / (a + b + c) := by
    field_simp
    nlinarith [habc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h7 : 1 / (c * a * (c + a) + 1) = b / (a + b + c) := by
    field_simp
    nlinarith [habc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h8 : a * b / (a^5 + b^5 + a * b) ≤ c / (a + b + c) := by linarith [h2, h5]

  have h9 : b * c / (b^5 + c^5 + b * c) ≤ a / (a + b + c) := by linarith [h3, h6]

  have h10 : c * a / (c^5 + a^5 + c * a) ≤ b / (a + b + c) := by linarith [h4, h7]

  have h11 : a * b / (a^5 + b^5 + a * b) + b * c / (b^5 + c^5 + b * c) + c * a / (c^5 + a^5 + c * a) ≤ c / (a + b + c) + a / (a + b + c) + b / (a + b + c) := by linarith [h8, h9, h10]

  have h12 : c / (a + b + c) + a / (a + b + c) + b / (a + b + c) = 1 := by
    field_simp
    <;> nlinarith

  linarith [h11, h12]