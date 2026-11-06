import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_257133 (a : ℝ) (ha : 0 < a) :
    IsGreatest {y | ∃ x, 0 < x ∧ y = 2 * sqrt (a * x - x^2)} a := by
  constructor
  · -- Show that a is in the set
    use a / 2
    constructor
    · -- Show that 0 < a / 2
      linarith
    · -- Show that a = 2 * sqrt (a * (a / 2) - (a / 2) ^ 2)
      have h2 : sqrt (a * (a / 2) - (a / 2) ^ 2) = a / 2 := by
        have h3 : a * (a / 2) - (a / 2) ^ 2 = (a ^ 2 / 4) := by
          nlinarith
        rw [h3]
        have h4 : sqrt (a ^ 2 / 4) = a / 2 := by
          have h5 : a > 0 := ha
          have h6 : a ^ 2 / 4 = (a / 2) ^ 2 := by
            ring_nf
          rw [h6]
          rw [Real.sqrt_sq (by linarith)]
        exact h4
      have h_eq : a = 2 * sqrt (a * (a / 2) - (a / 2) ^ 2) := by
        have h4 : sqrt (a * (a / 2) - (a / 2) ^ 2) = a / 2 := h2
        have h7 : 2 * sqrt (a * (a / 2) - (a / 2) ^ 2) = a := by 
          rw [h4]
          linarith
        linarith [h7]
      exact h_eq
  · -- Show that a is greatest
    intro y hy
    rcases hy with ⟨x, hx_pos, h_eq⟩
    have h3 : a * x - x^2 ≤ (a ^ 2 / 4) := by
      nlinarith [sq_nonneg (x - a / 2), mul_pos ha (show 0 < x by linarith)]
    have h4 : sqrt (a * x - x^2) ≤ (a / 2) := by
      have h5 : a * x - x^2 ≤ (a ^ 2 / 4) := h3
      have h6 : sqrt (a * x - x^2) ≤ sqrt (a ^ 2 / 4) := by
        apply Real.sqrt_le_sqrt
        linarith
      have h7 : sqrt (a ^ 2 / 4) = a / 2 := by
        have h8 : a > 0 := ha
        have h9 : a ^ 2 / 4 = (a / 2) ^ 2 := by
          ring_nf
        rw [h9]
        rw [Real.sqrt_sq (by linarith)]
      have h6 : sqrt (a * x - x^2) ≤ sqrt (a ^ 2 / 4) := by
        apply Real.sqrt_le_sqrt
        linarith
      nlinarith [h7, h6, Real.sqrt_nonneg (a * x - x^2)]
    have h5 : 2 * sqrt (a * x - x^2) ≤ a := by
      nlinarith
    have h_eq : y = 2 * sqrt (a * x - x^2) := by
      linarith [h_eq]
    linarith [h_eq, h5]