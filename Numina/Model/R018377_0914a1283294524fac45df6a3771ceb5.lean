import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_299898 :
  {x : ℝ | abs (x^2 - 2) ≤ 2 * x + 1} =
  {x | sqrt 2 - 1 ≤ x ∧ x ≤ 3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume abs (x^2 - 2) ≤ 2 * x + 1, prove sqrt 2 - 1 ≤ x ∧ x ≤ 3
    intro h
    have h1 : - (2 * x + 1) ≤ x^2 - 2 := by
      linarith [abs_le.mp h]
    have h2 : x^2 - 2 ≤ 2 * x + 1 := by
      linarith [abs_le.mp h]

    have h3 : x ≤ 3 := by
      nlinarith
    have h4 : sqrt 2 - 1 ≤ x := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (x + 1)]
    constructor
    · -- Show that sqrt 2 - 1 ≤ x
      exact h4
    · -- Show that x ≤ 3
      exact h3
  · -- Assume sqrt 2 - 1 ≤ x ∧ x ≤ 3, prove abs (x^2 - 2) ≤ 2 * x + 1
    rintro ⟨h1, h2⟩
    have h3 : x ^ 2 - 2 ≤ 2 * x + 1 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (x - 3), sq_nonneg (x - (-1 + Real.sqrt 2))]
    have h4 : x ^ 2 - 2 ≥ - (2 * x + 1) := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (x - 3), sq_nonneg (x - (-1 + Real.sqrt 2))]
    apply abs_le.mpr
    constructor <;> nlinarith