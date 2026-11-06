import Mathlib

theorem inequalities_299138 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^3 + b^3 + c^3 = 3) :
    1 ≤ 1 / (a^2 + a + 1) + 1 / (b^2 + b + 1) + 1 / (c^2 + c + 1) := by
  have h1 : ∀ x : ℝ, 0 < x → 1 / (x^2 + x + 1) ≥ (2 / 3) - (x / 3) := by
    intro x hx
    have hx1 : x ^ 2 + x + 1 > 0 := by
      have h1 : x ^ 2> 0 := by nlinarith
      nlinarith
    have h2 : (1 / (x ^ 2 + x + 1)) ≥ (2 / 3 - x / 3) := by 
      have h3 : x ^ 2 + x + 1 > 0 := hx1
      apply (le_div_iff₀ (by linarith)).mpr
      nlinarith [sq_nonneg (x - 1)]
    linarith
  have h2a : 1 / (a^2 + a + 1) ≥ (2 / 3) - (a / 3) := h1 a ha
  have h2b : 1 / (b^2 + b + 1) ≥ (2 / 3) - (b / 3) := h1 b hb
  have h2c : 1 / (c^2 + c + 1) ≥ (2 / 3) - (c / 3) := h1 c hc
  have h3 : a + b + c ≤ 3 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  -- Now prove that the inequality holds by substituting the derived bounds.
  have h4 : 1 / (a^2 + a + 1) + 1 / (b^2 + b + 1) + 1 / (c^2 + c + 1) ≥ 1 := by
    have h5 : 1 / (a^2 + a + 1) + 1 / (b^2 + b + 1) + 1 / (c^2 + c + 1) ≥ (2 / 3 - a / 3) + (2 / 3 - b / 3) + (2 / 3 - c / 3) := by
      linarith [h2a, h2b, h2c]
    have h6 : (2 / 3 - a / 3) + (2 / 3 - b / 3) + (2 / 3 - c / 3) = 2 - (a + b + c) / 3 := by
      linarith
    rw [h6] at h5
    -- The goal is now `2 - (a + b + c) / 3 ≤ 1 / (a^2 + a + 1) + 1 / (b^2 + b + 1) + 1 / (c^2 + c + 1)`.
    -- Which is exactly `2 - (a + b + c) / 3 ≤ 1`.
    nlinarith [h3]
  linarith