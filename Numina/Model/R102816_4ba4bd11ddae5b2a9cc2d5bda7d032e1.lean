import Mathlib

open Real

theorem inequalities_261377 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a * b / (a ^ 5 + b ^ 5 + a * b) +
    b * c / (b ^ 5 + c ^ 5 + b * c) +
    c * a / (c ^ 5 + a ^ 5 + c * a) ≤ 1 := by

  have h1 : ∀ x y : ℝ, x > 0 → y > 0 → x^5 + y^5 ≥ x^2 * y^2 * (x + y) := by
    intro x y hx hy
    suffices h : x^5 + y^5 - x^2 * y^2 * (x + y) ≥ 0 by linarith
    have h2 : x^5 + y^5 - x^2 * y^2 * (x + y) = (x - y)^2 * (x + y) * (x^2 + x * y + y^2) := by
      ring
    rw [h2]
    positivity

  have h2 : a * b / (a ^ 5 + b ^ 5 + a * b) ≤ 1 / (a * b * (a + b) + 1) := by
    have h3 : a ^ 5 + b ^ 5 ≥ a^2 * b^2 * (a + b) := by
      nlinarith [h1 a b ha hb, sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a * b - 1), sq_nonneg (a * b + 1)]
    have h4 : a ^ 5 + b ^ 5 + a * b ≥ a * b * (a * b * (a + b) + 1) := by
      nlinarith [h3, sq_nonneg (a * b - 1), sq_nonneg (a * b + 1)]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * b + 1)]

  have h4 : b * c / (b ^ 5 + c ^ 5 + b * c) ≤ 1 / (b * c * (b + c) + 1) := by
    have h3 : b ^ 5 + c ^ 5 ≥ b^2 * c^2 * (b + c) := by
      nlinarith [h1 b c hb hc, sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b - c), sq_nonneg (b * c - 1), sq_nonneg (b * c + 1)]
    have h4 : b ^ 5 + c ^ 5 + b * c ≥ b * c * (b * c * (b + c) + 1) := by
      nlinarith [h3, sq_nonneg (b * c - 1), sq_nonneg (b * c + 1)]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (b * c - 1), sq_nonneg (b * c + 1)]

  have h5 : c * a / (c ^ 5 + a ^ 5 + c * a) ≤ 1 / (c * a * (c + a) + 1) := by
    have h3 : c ^ 5 + a ^ 5 ≥ c^2 * a^2 * (c + a) := by
      nlinarith [h1 c a hc ha, sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c - a), sq_nonneg (c * a - 1), sq_nonneg (c * a + 1)]
    have h4 : c ^ 5 + a ^ 5 + c * a ≥ c * a * (c * a * (c + a) + 1) := by
      nlinarith [h3, sq_nonneg (c * a - 1), sq_nonneg (c * a + 1)]
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (c * a - 1), sq_nonneg (c * a + 1)]

  have h6 : 1 / (a * b * (a + b) + 1) + 1 / (b * c * (b + c) + 1) + 1 / (c * a * (c + a) + 1) = 1 := by
    rw [show c = 1 / (a * b) by
      field_simp [show a * b ≠ 0 by positivity]
      nlinarith [habc]
    ]
    field_simp [show a * b ≠ 0 by positivity, show 1 + b * (1 / (a * b)) * (b + 1 / (a * b)) ≠ 0 by positivity, show 1 + (1 / (a * b)) * a * ((1 / (a * b)) + a) ≠ 0 by positivity]
    nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), sq_nonneg (a * b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1)]

  linarith [h2, h4, h5, h6]