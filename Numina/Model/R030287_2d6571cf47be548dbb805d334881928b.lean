import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_160549 (x : ℝ) :
  x ∈ Icc (-1) 2 ↔ ∃ y, y ∈ Icc (-π / 2) (π / 2) ∧
  (2 * x - 1) / 3 = sin y := by
  constructor
  · -- Assume x ∈ Icc (-1) 2, we need to prove ∃ y, y ∈ Icc (-π / 2) (π / 2) ∧ (2 * x - 1) / 3 = sin y
    intro hx
    rcases hx with ⟨hx1, hx2⟩
    use arcsin ((2 * x - 1) / 3)
    constructor
    · -- Show y ∈ Icc (-π / 2) (π / 2)
      have h1 : -1 ≤ (2 * x - 1) / 3 := by
        linarith
      have h2 : (2 * x - 1) / 3 ≤ 1 := by
        linarith
      constructor
      · -- Show -π / 2 ≤ arcsin ((2 * x - 1) / 3)
        have h3 : -(Real.pi / 2) ≤ arcsin ((2 * x - 1) / 3) := by
          apply Real.neg_pi_div_two_le_arcsin
        linarith [h3]
      · -- Show arcsin ((2 * x - 1) / 3) ≤ π / 2
        have h4 : arcsin ((2 * x - 1) / 3) ≤ Real.pi / 2 := by
          apply Real.arcsin_le_pi_div_two
        linarith [h4]
    · -- Show (2 * x - 1) / 3 = sin y
      have h5 : sin (arcsin ((2 * x - 1) / 3)) = (2 * x - 1) / 3 := by
        apply Real.sin_arcsin
        all_goals
          linarith
      linarith [h5]
  · -- Assume ∃ y, y ∈ Icc (-π / 2) (π / 2) ∧ (2 * x - 1) / 3 = sin y, prove x ∈ Icc (-1) 2
    rintro ⟨y, hy, heq⟩
    rcases hy with ⟨hy1, hy2⟩
    have h1 : -1 ≤ sin y := Real.neg_one_le_sin y
    have h2 : sin y ≤ 1 := Real.sin_le_one y
    have h5 : -1 ≤ (2 * x - 1) / 3 := by
      nlinarith [heq, h1]
    have h6 : (2 * x - 1) / 3 ≤ 1 := by
      nlinarith [heq, h2]
    constructor
    · -- Show -1 ≤ x
      nlinarith
    · -- Show x ≤ 2
      nlinarith