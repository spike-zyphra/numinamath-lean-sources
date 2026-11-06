import Mathlib

open Set Real

theorem algebra_232334 {a : ℝ} (ha : 2 * a + 1 ≤ 3 * a - 5) :
    {x | 2 * a + 1 ≤ x ∧ x ≤ 3 * a - 5} ⊆ {x | 3 ≤ x ∧ x ≤ 22} ↔
    6 ≤ a ∧ a ≤ 9 := by

  constructor
  · -- Assume subset
    intro h
    have h1 : 6 ≤ a := by
      linarith
    have h2 : a ≤ 9 := by
      have h3a5 : (3 * a - 5 : ℝ) ∈ {x | 2 * a + 1 ≤ x ∧ x ≤ 3 * a - 5} := by
        constructor
        · linarith
        · linarith
      have h4 : (3 * a - 5 : ℝ) ∈ {x | 3 ≤ x ∧ x ≤ 22} := h h3a5
      have h5 : (3 * a - 5 : ℝ) ≤ 22 := h4.right
      linarith
    exact ⟨h1, h2⟩
  · -- Assume 6 ≤ a ∧ a ≤ 9, prove subset
    rintro ⟨ha1, ha2⟩
    intro x hx
    have h3 : 2 * a + 1 ≤ x := hx.left
    have h4 : x ≤ 3 * a - 5 := hx.right
    constructor
    · -- Show 3 ≤ x
      linarith [ha1, h3]
    · -- Show x ≤ 22
      linarith [ha2, h4]