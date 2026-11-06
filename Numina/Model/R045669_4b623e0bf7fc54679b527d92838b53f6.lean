import Mathlib

def isAwesome (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∀ q : ℕ, q < p → Nat.Prime (p + 2 * q)

theorem number_theory_87809 :
    IsGreatest {p | isAwesome p} 3 := by
  constructor
  · -- Show that 3 is indeed in the set
    show isAwesome 3
    constructor
    · -- 3 is prime
      norm_num
    · -- ∀ q < 3, 3 + 2q is prime
      intro q hq
      interval_cases q <;> norm_num
  · -- Show that 3 is the greatest element in the set
    intro p hp
    rcases hp with ⟨h_prime, h⟩
    by_contra h3
    push_neg at h3
    have h1 := h 1 (by linarith)
    have h2 := h 2 (by linarith)
    have h3' : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
      omega
    rcases h3' with (h3' | h3' | h3')
    · -- Assume p % 3 = 0
      have h4 : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
      contradiction
    · -- Assume p % 3 = 1
      have h6 : (p + 2 * 1) % 3 = 0 := by
        omega
      have h7 : ¬ Nat.Prime (p + 2 * 1) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 2 * 1) by omega) (by omega) (by omega)
      have h8 : Nat.Prime (p + 2 * 1) := h1
      -- Contradiction
      exact h7 h8
    · -- Assume p % 3 = 2
      have h8 : (p + 2 * 2) % 3 = 0 := by
        omega
      have h9 : ¬ Nat.Prime (p + 2 * 2) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 2 * 2) by omega) (by omega) (by omega)
      have h10 : Nat.Prime (p + 2 * 2) := h2
      -- Contradiction
      exact h9 h10