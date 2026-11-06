import Mathlib

theorem inequalities_598108 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 3) :
    1 ≤ 1 / (a^3 + 2) + 1 / (b^3 + 2) + 1 / (c^3 + 2) := by

  have h1 : ∀ x : ℝ, 0 < x → 1 / (x^3 + 2) ≥ (3 - x^2) / 6 := by
    intro x hx
    have h2 : x ^ 2 * (x - 1) ^ 2 * (x + 2) ≥ 0 := by
      have h11 : x ^ 2 ≥ 0 := sq_nonneg x
      have h12 : (x - 1) ^ 2 ≥ 0 := sq_nonneg (x - 1)
      have h13 : x + 2 > 0 := by nlinarith [hx]
      apply mul_nonneg
      apply mul_nonneg
      all_goals linarith
    have h3 : (3 - x^2) * (x^3 + 2) ≤ 6 := by
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1), sq_nonneg (x * (x - 1)), sq_nonneg (x * (x - 2)), sq_nonneg ((x - 1) * (x + 2)), sq_nonneg (x ^ 2 - x)]
    have h4 : (3 - x^2) / 6 ≤ 1 / (x^3 + 2) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    linarith

  have h2a : 1 / (a^3 + 2) ≥ (3 - a^2) / 6 := h1 a ha
  have h2b : 1 / (b^3 + 2) ≥ (3 - b^2) / 6 := h1 b hb
  have h2c : 1 / (c^3 + 2) ≥ (3 - c^2) / 6 := h1 c hc

  have h3 : 1 / (a^3 + 2) + 1 / (b^3 + 2) + 1 / (c^3 + 2) ≥ (3 - a^2) / 6 + (3 - b^2) / 6 + (3 - c^2) / 6 := by
    linarith [h2a, h2b, h2c]

  have h4 : (3 - a^2) / 6 + (3 - b^2) / 6 + (3 - c^2) / 6 = (9 - (a^2 + b^2 + c^2)) / 6 := by
    ring

  have h5 : (9 - (a^2 + b^2 + c^2)) / 6 = 1 := by
    rw [show a^2 + b^2 + c^2 = 3 by linarith]
    norm_num

  linarith [h3, h4, h5]