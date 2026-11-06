import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_170407 (m : ℝ) :
  (∀ x : ℝ, (x^2 + m * x - 1) / (2 * x^2 - 2 * x + 3) < 1) ↔ m ∈ Ioo (-6) 2 := by
  constructor
  · -- Assume that for all real numbers x, (x^2 + m * x - 1) / (2 * x^2 - 2 * x + 3) < 1, prove that m ∈ (-6, 2).
    intro h
    have h1 : -6 < m := by
      have h2 := h (-2)
      norm_num at h2
      linarith
    have h2 : m < 2 := by
      have h3 := h 2
      norm_num at h3
      linarith
    exact ⟨h1, h2⟩
  · -- Assume m ∈ (-6, 2), prove that ∀ x : ℝ, (x^2 + m * x - 1) / (2 * x^2 - 2 * x + 3) < 1.
    rintro ⟨hm1, hm2⟩
    intro x
    have h1 : 0 < (2 * x ^ 2 - 2 * x + 3) := by
      nlinarith [sq_nonneg (x - 1 / 2)]
    have h2 : (x ^ 2 + m * x - 1) < (2 * x ^ 2 - 2 * x + 3) := by
      have h3 : x ^ 2 - (m + 2) * x + 4 > 0 := by 
        nlinarith [sq_nonneg (x - (m + 2) / 2), sq_nonneg (m + 6), sq_nonneg (2 - m), 
                  mul_pos (show 0 < (2 - m) by linarith) (show 0 < (m + 6) by linarith),
                  sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (m - 2), sq_nonneg (m + 6)]
      nlinarith
    apply (div_lt_iff₀ h1).mpr
    linarith