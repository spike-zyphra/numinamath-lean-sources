import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_190072 (a : ℝ) :
  (∀ x : ℝ, x^2 - x + 1 ≠ 0 → -3 < (x^2 + a * x - 2) / (x^2 - x + 1) ∧
    (x^2 + a * x - 2) / (x^2 - x + 1) < 2) ↔ a < 2 ∧ a > -1 := by
  constructor
  · -- Forward direction: Assume the inequality holds for all x, prove -1 < a < 2
    intro h
    have h1 := h (1 / 2) (by norm_num)
    norm_num at h1
    have h2 := h 0 (by norm_num)
    norm_num at h2
    have h3 := h 1 (by norm_num)
    norm_num at h3
    have h4 := h 2 (by norm_num)
    norm_num at h4
    have h5 := h 3 (by norm_num)
    norm_num at h5
    constructor
    · -- Show a < 2
      nlinarith [h1, h2, h3, h4, h5]
    · -- Show a > -1
      nlinarith [h1, h2, h3, h4, h5]
  · -- Reverse direction: Assume -1 < a < 2, prove the inequality holds for all x
    rintro ⟨ha2, ha1⟩
    intro x hx
    have h1 : x^2 - x + 1 > 0 := by
      nlinarith [sq_nonneg (x - 1 / 2)]
    constructor
    · -- Show -3 < (x^2 + a * x - 2) / (x^2 - x + 1)
      have h1' : x^2 - x + 1 > 0 := h1
      apply (lt_div_iff₀ h1').mpr
      have h3 : 4 * x^2 + (a - 3) * x + 1 > 0 := by
        nlinarith [sq_nonneg (x + (a - 3) / 8), sq_nonneg (x - 1 / 2), sq_nonneg (a + 1), sq_nonneg (a - 2), sq_nonneg (x - 2), sq_nonneg (x + 1), sq_nonneg (x - 1)]
      linarith
    · -- Show (x^2 + a * x - 2) / (x^2 - x + 1) < 2
      have h1' : x^2 - x + 1 > 0 := h1
      apply (div_lt_iff₀ h1').mpr
      have h4 : x^2 + a * x - 2 < 2 * (x^2 - x + 1) := by
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 1), sq_nonneg (x - (a + 2) / 2), sq_nonneg (a + 2), sq_nonneg (x - 1), sq_nonneg (x - a)]
      linarith