import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_323113 (f : ℝ → ℝ) (hf : f = λ x => sqrt (x * (x ^ 2 + 8) * (8 - x)) / (x + 1)) :
    ∀ x ∈ Icc 0 8, f x ∈ Icc 0 4 := by
  intro x hx
  rw [hf]
  rcases hx with ⟨hx1, hx2⟩
  have h1 : 0 ≤ sqrt (x * (x ^ 2 + 8) * (8 - x)) / (x + 1) := by
    have h2 : 0 ≤ sqrt (x * (x ^ 2 + 8) * (8 - x)) := Real.sqrt_nonneg (x * (x ^ 2 + 8) * (8 - x))
    have h3 : 0 < x + 1 := by linarith
    apply div_nonneg
    . exact h2
    . linarith
  have h2 : sqrt (x * (x ^ 2 + 8) * (8 - x)) / (x + 1) ≤ 4 := by
    have h3 : sqrt (x * (x ^ 2 + 8) * (8 - x)) ≤ 4 * (x + 1) := by
      have h4 : 0 ≤ x * (x ^ 2 + 8) * (8 - x) := by
        apply mul_nonneg
        apply mul_nonneg
        . linarith
        . nlinarith
        . linarith
      have h5 : 0 ≤ (4 * (x + 1)) := by nlinarith
      have h6 : sqrt (x * (x ^ 2 + 8) * (8 - x)) ≤ 4 * (x + 1) := by
        apply Real.sqrt_le_iff.mpr
        constructor
        . nlinarith
        . nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 1)]
        all_goals nlinarith
      exact h6
    have h4 : 0 < x + 1 := by linarith
    have h8 : sqrt (x * (x ^ 2 + 8) * (8 - x)) / (x + 1) ≤ 4 := by
      have h9 : 0 < x + 1 := by linarith
      have h10 : sqrt (x * (x ^ 2 + 8) * (8 - x)) ≤ 4 * (x + 1) := h3
      have h11 : sqrt (x * (x ^ 2 + 8) * (8 - x)) / (x + 1) ≤ (4 * (x + 1)) / (x + 1) := by
        apply (div_le_div_right h9).mpr
        linarith
      have h12 : (4 * (x + 1)) / (x + 1) = 4 := by
        have h13 : x + 1 ≠ 0 := by linarith
        field_simp [h13]
        all_goals nlinarith
      linarith [h12, h11]
    linarith
  constructor
  . exact h1
  . exact h2