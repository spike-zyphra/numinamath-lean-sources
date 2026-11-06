import Mathlib

open Set Real

theorem algebra_215358 {M N : Set ℝ}
    (hM : M = {x | -1 / 2 < x ∧ x < 1 / 2}) (hN : N = {x | x ^ 2 ≤ x}) :
    M ∩ N = {x | 0 ≤ x ∧ x < 1 / 2} := by
  ext x
  simp [hM, hN]
  constructor
  · -- Assume x ∈ M ∩ N
    rintro ⟨⟨h1, h2⟩, h3⟩
    constructor
    · -- Show that 0 ≤ x
      nlinarith
    · -- Show that x < 1/2
      linarith
  · -- Assume x ∈ {x | 0 ≤ x ∧ x < 1 / 2}
    rintro ⟨h1, h2⟩
    constructor
    · -- Show that x ∈ M
      constructor
      · -- Show that -1/2 < x
        linarith
      · -- Show that x < 1/2
        linarith
    · -- Show that x ∈ N
      nlinarith [sq_nonneg (x - 0), sq_nonneg (x - 1)]