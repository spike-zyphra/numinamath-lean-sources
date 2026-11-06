import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_279692 (a : ℝ) :
  (∀ x ∈ Ici (-1), x^2 - 2*a*x + 2 ≥ a) ↔ a ∈ Icc (-3) 1 := by
  constructor
  · -- Assume that for all x >= -1, x^2 - 2*a*x + 2 >= a, prove that a ∈ Icc (-3, 1).
    intro h
    have h1 := h (-1) (mem_Ici.mpr (show (-1 : ℝ) ≥ -1 by norm_num))
    have h2 := h 1 (mem_Ici.mpr (show (1 : ℝ) ≥ -1 by norm_num))
    have h3 : a ≥ -3 := by nlinarith
    have h4 : a ≤ 1 := by nlinarith
    exact ⟨h3, h4⟩
  · -- Assume a ∈ Icc (-3, 1), prove that ∀ x ∈ Ici (-1), x^2 - 2*a*x + 2 ≥ a.
    rintro ⟨h1, h2⟩
    intro x hx
    have hx' : x ≥ -1 := hx
    have h3 : x ^ 2 - 2 * a * x + 2 ≥ a := by
      by_cases h : x ≥ a
      · -- Case where x >= a
        nlinarith [sq_nonneg (x - a), sq_nonneg (x + 1), sq_nonneg (a + 3), sq_nonneg (a - 1)]
      · -- Case where x < a
        nlinarith [sq_nonneg (x - a), sq_nonneg (x + 1), sq_nonneg (a + 3), sq_nonneg (a - 1)]
    linarith