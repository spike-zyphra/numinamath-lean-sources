import Mathlib

theorem number_theory_235826 (n : ℕ) (h₀ : n > 0) (h₁ : n ≤ 2005 - 17) :
    ∃ m ∈ Finset.Icc n (n + 17), m % (Nat.digits 10 m).sum = 0 := by

  have h2 : n ≤ 2005 - 17 := h₁
  have h3 : n + 17 ≤ 2005 := by omega

  have : ∃ m ∈ Finset.Icc n (n + 17), m % (Nat.digits 10 m).sum = 0 := by
    interval_cases n <;> native_decide
    <;> try { tauto }
  exact this