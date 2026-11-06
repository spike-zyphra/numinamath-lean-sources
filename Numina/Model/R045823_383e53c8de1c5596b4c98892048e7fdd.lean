import Mathlib

theorem number_theory_310862 (a : ℕ) (ha : a > 0) :
    Nat.Prime a ∧ Nat.Prime (a + 8) ∧ Nat.Prime (a + 16) ↔ a = 3 := by
  constructor
  · -- Assume Nat.Prime a ∧ Nat.Prime (a + 8) ∧ Nat.Prime (a + 16), prove a = 3
    intro h
    rcases h with ⟨h1, h2, h3⟩
    by_cases h4 : a ≤ 23
    · interval_cases a <;> norm_num at h1 h2 h3 ⊢ <;> try tauto
    · -- a > 23
      have h5 : a % 3 = 1 ∨ a % 3 = 2 := by
        by_contra h
        push_neg at h
        have h6 : a % 3 = 0 := by omega
        have h7 : ¬ Nat.Prime a := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ a by omega)
          all_goals omega
        contradiction
      rcases h5 with (h5 | h5)
      · -- a % 3 = 1
        have h8 : (a + 8) % 3 = 0 := by
          omega
        have h9 : ¬ Nat.Prime (a + 8) := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (a + 8) by omega)
          all_goals omega
        contradiction
      · -- a % 3 = 2
        have h10 : (a + 16) % 3 = 0 := by
          omega
        have h11 : ¬ Nat.Prime (a + 16) := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (a + 16) by omega)
          all_goals omega
        contradiction
  · -- Assume a = 3, prove Nat.Prime a ∧ Nat.Prime (a + 8) ∧ Nat.Prime (a + 16)
    intro h
    rw [h]
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num