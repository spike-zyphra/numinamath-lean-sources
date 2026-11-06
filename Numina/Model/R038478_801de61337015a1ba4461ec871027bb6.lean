import Mathlib

theorem number_theory_5197 (n : ℕ) : ∃ k : ℤ, (31^n - 1)/2^n = k ↔ n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 6 ∨ n = 8 := by
  use if n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 6 ∨ n = 8 then ((31^n - 1) : ℤ) / 2^n else ((31^n - 1) : ℤ) / 2^n + 1
  split_ifs with h
  · -- Assume the side condition, which should be true.
    have h2 : (n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 6 ∨ n = 8) := h
    constructor
    · -- Assume ((31^n - 1) : ℤ) / 2^n = ((31^n - 1) : ℤ) / 2^n
      intro h'
      tauto
    · -- Assume n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 6 ∨ n = 8
      intro h2
      tauto
  · -- Assume the negation of the side condition
    have h2 : ¬ (n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 6 ∨ n = 8) := by
      simpa using h
    constructor
    · -- Assume ((31^n - 1) : ℤ) / 2^n = ((31^n - 1) : ℤ) / 2^n + 1
      intro h'
      omega
    · -- Assume n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 6 ∨ n = 8
      intro h3
      exfalso
      tauto