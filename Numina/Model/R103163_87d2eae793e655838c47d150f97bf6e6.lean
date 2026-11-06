import Mathlib

theorem number_theory_272956 (p : ℕ) (hp : Nat.Prime p) (h : 5 ≤ p) :
    24 ∣ (p ^ 2 - 1) := by 
  have h1 : p % 2 ≠ 0 := by 
    by_contra h2
    have h3 : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) 
      all_goals omega
    contradiction

  have h4 : p % 3 ≠ 0 := by 
    by_contra h5
    have h6 : 3 ∣ p := by
      omega
    have h7 : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt h6 
      all_goals omega
    contradiction

  have h8 : (p ^ 2) % 8 = 1 := by
    have h81 : p % 2 ≠ 0 := h1
    have h82 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by 
      omega 
    rcases h82 with (h82 | h82 | h82 | h82)
    · -- Case p ≡ 1 [MOD 8]
      norm_num [Nat.pow_mod, h82]
    · -- Case p ≡ 3 [MOD 8]
      norm_num [Nat.pow_mod, h82]
    · -- Case p ≡ 5 [MOD 8]
      norm_num [Nat.pow_mod, h82]
    · -- Case p ≡ 7 [MOD 8]
      norm_num [Nat.pow_mod, h82]

  have h9 : (p ^ 2) % 3 = 1 := by 
    have h91 : p % 3 ≠ 0 := h4
    have h92 : p % 3 = 1 ∨ p % 3 = 2 := by 
      omega 
    rcases h92 with (h92 | h92)
    · -- Case p ≡ 1 [MOD 3]
      norm_num [Nat.pow_mod, h92]
    · -- Case p ≡ 2 [MOD 3]
      norm_num [Nat.pow_mod, h92]

  omega