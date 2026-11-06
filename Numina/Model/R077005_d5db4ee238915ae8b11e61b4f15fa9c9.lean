import Mathlib

theorem algebra_156958 (k l : ℤ) : 5 * k + 3 * l = 32 ↔ ∃ x, k = 3 * x - 32 ∧ l = 64 - 5 * x := by
  constructor
  · -- Forward implication: If 5k + 3l = 32, then there exists x with k = 3x - 32 and l = 64 - 5x.
    intro h
    have h1 : k % 3 = 1 := by
      omega
    use (k + 32) / 3
    constructor
    · -- Show k = 3 * x - 32.
      omega
    · -- Show l = 64 - 5 * x.
      omega
  · -- Backward direction: If there exists x such that k = 3x - 32 and l = 64 - 5x, then 5k + 3l = 32.
    rintro ⟨x, hk, hl⟩
    rw [hk, hl]
    linarith