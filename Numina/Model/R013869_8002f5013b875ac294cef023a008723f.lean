import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_299769 (a : ℝ) :
  {x | a + 1 ≤ x ∧ x < 2 * a - 1} ⊆ {x | -2 ≤ x ∧ x ≤ 5} ↔ a ≤ 3 := by
  constructor
  · -- Assume {x | a + 1 ≤ x ∧ x < 2 * a - 1} ⊆ {x | -2 ≤ x ∧ x ≤ 5} prove a ≤ 3
    intro h
    by_contra ha
    push_neg at ha
    have h1 : a > 3 := by linarith
    have h2 : a + 2 < 2 * a - 1 := by linarith
    have h3 : a + 1 ≤ a + 2 := by linarith
    have h4 : a + 2 < 2 * a - 1 := by linarith
    have h5 : (a + 2) ∈ {x | a + 1 ≤ x ∧ x < 2 * a - 1} := by
      constructor
      · linarith
      · linarith
    have h6 : (a + 2) ∈ {x | -2 ≤ x ∧ x ≤ 5} := h h5
    have h7 : -2 ≤ (a + 2) := by
      have h8 : (a + 2) ∈ {x | -2 ≤ x ∧ x ≤ 5} := h6
      exact h8.1
    have h8 : (a + 2) ≤ 5 := by
      have h8 : (a + 2) ∈ {x | -2 ≤ x ∧ x ≤ 5} := h6
      exact h8.2
    nlinarith
  · -- Assume a ≤ 3 prove {x | a + 1 ≤ x ∧ x < 2 * a - 1} ⊆ {x | -2 ≤ x ∧ x ≤ 5}
    intro ha x hx
    have h1 : a ≤ 3 := by linarith
    have h2 : a + 1 ≤ x := hx.1
    have h3 : x < 2 * a - 1 := hx.2
    have h4 : x ≤ 5 := by
      have h5 : 2 * a - 1 ≤ (5 : ℝ) := by
        linarith
      nlinarith
    have h6 : -2 ≤ x := by
      nlinarith
    exact ⟨h6, h4⟩