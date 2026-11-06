import Mathlib

open Set Real

theorem inequalities_12853 {M N : Set ℝ}
    (hM : M = {x | x ^ 2 - 2 * x - 3 ≤ 0}) (hN : N = {x | abs x < 2}) :
    M ∩ N = {x | -1 ≤ x ∧ x < 2} := by 
  ext x 
  simp [hM, hN]
  constructor
  · -- First, prove the forward direction: if x ∈ M ∩ N, then x ∈ {x | -1 ≤ x ∧ x < 2}
    rintro ⟨h1, h2⟩
    constructor
    · -- Show that -1 ≤ x from h1: x^2 - 2 * x - 3 ≤ 0
      cases' abs_lt.mp h2 with h3 h4
      nlinarith 
    · -- Show that x < 2 from h2: abs x < 2
      cases' abs_lt.mp h2 with h3 h4
      linarith 
  · -- Now prove the reverse direction: if x ∈ {x | -1 ≤ x ∧ x < 2}, then x ∈ M ∩ N
    rintro ⟨h1, h2⟩
    constructor
    · -- Show that x^2 - 2 * x - 3 ≤ 0 
      nlinarith 
    · -- Show that abs x < 2 
      have h3 : abs x < 2 := by 
        rw [abs_lt]
        constructor <;> linarith 
      simpa using h3