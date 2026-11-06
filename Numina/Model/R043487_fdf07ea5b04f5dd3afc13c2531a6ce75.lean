import Mathlib

theorem number_theory_160739 (x y : ℤ) : 7 * x - 3 * y = 2 ↔ ∃ k : ℤ, x = 3 * k + 2 ∧ y = 7 * k + 4 := by
  constructor
  · -- Assume 7 * x - 3 * y = 2, prove ∃ k : ℤ, x = 3 * k + 2 ∧ y = 7 * k + 4
    rintro h
    use (x - 2) / 3
    have hk : (x - 2) % 3 = 0 := by
      omega
    constructor
    · -- Prove x = 3 * k + 2
      omega
    · -- Prove y = 7 * k + 4
      omega
  · -- Assume ∃ k : ℤ, x = 3 * k + 2 ∧ y = 7 * k + 4, prove 7 * x - 3 * y = 2
    rintro ⟨k, hx, hy⟩
    have eq1 : 7 * x - 3 * y = 2 := by
      rw [hx, hy]
      linarith
    exact eq1