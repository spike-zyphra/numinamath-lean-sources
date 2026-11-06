import Mathlib

theorem number_theory_206574 (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ∃ x > 0, ∃ a b c d : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
      x = a ^ c + b ^ d ∧ Nat.Prime c ∧ Nat.Prime d ↔
    (∀ p ∈ P, Nat.Prime p) := by

  use 2
  constructor
  · norm_num
  use 1, 1, 2, 2
  constructor
  · -- Assume the left side is true, need to prove the right side
    intro h
    have h1 : ∀ p ∈ P, Nat.Prime p := hP
    exact h1
  · -- Assume the right side is true, need to prove the left side
    intro h
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num