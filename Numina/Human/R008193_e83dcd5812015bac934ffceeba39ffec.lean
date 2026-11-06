import Mathlib

theorem number_theory_128088 :
    (∀ n : ℕ, Nat.Prime (2 ^ n - 1) → Nat.Prime n) ∧
    ¬ (∀ n : ℕ, Nat.Prime n → Nat.Prime (2 ^ n - 1)) := by
  constructor
  . intro n h
    have h₁ : n ≠ 1 := by
      rintro rfl
      simp [Nat.not_prime_one] at h
    exact (Nat.prime_of_pow_sub_one_prime h₁ h).2
  . intro h
    specialize h 11
    absurd h
    native_decide