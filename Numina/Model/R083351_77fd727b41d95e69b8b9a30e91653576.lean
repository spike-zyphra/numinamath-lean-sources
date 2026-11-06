import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_151160 (ε : ℝ) (hε : ε > 0) :
  ∃ δ, δ > 0 ∧ ∀ x, (|x - 11| < δ ∧ x ≠ 11) → |(2 * x ^ 2 - 21 * x - 11) / (x - 11) - 23| < ε := by
    use ε / 2
    constructor
    · -- Show that δ > 0 using the hypothesis ε > 0
      linarith
    · -- Prove the main implication
      intro x h
      rcases h with ⟨h1, h2⟩
      have h3 : x - 11 ≠ 0 := by
        intro h'
        apply h2
        linarith
      have eqn : (2 * x ^ 2 - 21 * x - 11) / (x - 11) - 23 = 2 * (x - 11) := by
        have h4 : x - 11 ≠ 0 := h3
        field_simp [h4]
        ring
      have h5 : |(2 * (x - 11))| = 2 * |x - 11| := by
        rw [abs_mul]
        norm_num
      rw [eqn]
      rw [h5]
      linarith [abs_lt.mp h1]