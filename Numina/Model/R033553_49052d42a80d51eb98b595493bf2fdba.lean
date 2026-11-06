import Mathlib

open Real

theorem inequalities_244541 (k : ℝ) :
    (∀ a b : ℝ, a > 0 → b > 0 → (a + b) * (a * b + 1) * (b + 1) ≥ k * a * b ^ 2) ↔
    k ≤ 27 / 4 := by
  constructor
  · -- First, we show that k ≤ 27/4 is necessary.
    intro h
    have h1 := h 1 2 (by norm_num) (by norm_num)
    norm_num at h1
    linarith
  · -- Now, we show that k ≤ 27/4 is sufficient.
    intro hk a b ha hb
    have h1 : (a + b) * (a * b + 1) * (b + 1) ≥ (27 / 4) * a * b ^ 2 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (b * (a - 1)), sq_nonneg (a * (b - 2)), sq_nonneg (b - 2 * a), sq_nonneg (a * b - 2), sq_nonneg (a - 1), sq_nonneg (b - 2), mul_pos ha hb, mul_pos ha (show 0 < a * b from mul_pos ha hb), mul_pos (show 0 < a * b from mul_pos ha hb) hb, sq_nonneg (a * b - 2 * a), sq_nonneg (a * b - a), sq_nonneg (b - 2 * a)]
    have h2 : (a + b) * (a * b + 1) * (b + 1) ≥ k * a * b ^ 2 := by
      have h3 : k ≤ 27 / 4 := by linarith
      nlinarith [h1, h3, mul_pos ha hb, mul_pos ha (show 0 < b ^ 2 by positivity), mul_pos (show 0 < a * b from mul_pos ha hb) hb]
    exact h2