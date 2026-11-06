import Mathlib

open Set Real

theorem algebra_9020 {M N : Set ℝ}
    (hM : M = {x | x ^ 2 - 2 * x - 3 < 0}) (hN : N = {x | 2 * x < 2}) :
    M ∩ (Set.compl N) = {x | 1 ≤ x ∧ x < 3} := by
  ext x
  simp [hM, hN, Set.compl]
  constructor
  · -- Assume x ∈ M ∩ (Set.compl N)
    rintro ⟨h1, h2⟩
    constructor
    · -- Show that 1 ≤ x
      nlinarith
    · -- Show that x < 3
      nlinarith
  · -- Assume 1 ≤ x ∧ x < 3, prove x ∈ M ∩ (Set.compl N)
    rintro ⟨h1, h2⟩
    constructor
    · -- Show that x ∈ M
      nlinarith
    · -- Show that x ∉ N
      nlinarith