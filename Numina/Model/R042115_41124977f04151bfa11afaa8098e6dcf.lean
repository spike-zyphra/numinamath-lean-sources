import Mathlib

theorem number_theory_245547 (n : ℕ) (h₀ : n < 1000) :
    579000 + n ≡ 0 [MOD 5] ∧ 579000 + n ≡ 0 [MOD 7] ∧ 579000 + n ≡ 0 [MOD 9] ↔
    (n = 600 ∨ n = 285 ∨ n = 915) := by 
  constructor
  · -- Assume the conjunction of the divisibility conditions, prove the disjunction of possible values for n.
    intro h
    rcases h with ⟨h1, h2, h3⟩
    norm_num [Nat.ModEq] at h1 h2 h3
    have h4 : n % 5 = 0 := by 
      omega
    have h5 : n % 7 = 5 := by
      omega
    have h6 : n % 9 = 6 := by
      omega
    have h7 : n % 315 = 285 := by
      omega
    have h8 : n = 285 ∨ n = 600 ∨ n = 915 := by
      omega
    tauto
  · -- Assume the disjunction of possible values for n, prove the conjunction of divisibility conditions.
    rintro (h | h | h)
    · -- Case n = 600
      rw [h]
      constructor
      · norm_num [Nat.ModEq]
      constructor
      · norm_num [Nat.ModEq]
      · norm_num [Nat.ModEq]
    · -- Case n = 285
      rw [h]
      constructor
      · norm_num [Nat.ModEq]
      constructor
      · norm_num [Nat.ModEq]
      · norm_num [Nat.ModEq]
    · -- Case n = 915
      rw [h]
      constructor
      · norm_num [Nat.ModEq]
      constructor
      · norm_num [Nat.ModEq]
      · norm_num [Nat.ModEq]