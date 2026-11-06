import Mathlib

open Real

theorem inequalities_25699 (k : ℝ) :
    (∀ a b : ℝ, a > 0 → b > 0 → (a + b) * (a * b + 1) * (b + 1) ≥ k * a * b ^ 2) ↔
    k ≤ 27 / 4 := by
  constructor
  · -- First implication: if inequality holds for all a,b, then k ≤ 27/4.
    intro h
    have h2 := h 1 2 (by norm_num) (by norm_num)
    norm_num at h2 ⊢
    all_goals linarith
  · -- If k ≤ 27/4, then inequality holds for all a,b
    intro hk a b ha hb
    have h1 : (a + b) * (a * b + 1) * (b + 1) ≥ (27 / 4) * a * b ^ 2 := by
      nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (b - 2), sq_nonneg (a * b - 2), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a * (b - 2)), sq_nonneg ((a - 1) * (b - 2)), sq_nonneg (a * b), sq_nonneg (a - b), mul_pos ha hb, mul_pos ha (show b > 0 by linarith), mul_pos (show b > 0 by linarith) ha]
    have hk1 : k * a * b ^ 2 ≤ (a * b ^ 2) * (27 / 4) := by
      have hk2 : k ≤ 27 / 4 := by linarith
      have h3 : a * b ^ 2 > 0 := by
        positivity
      nlinarith
    nlinarith