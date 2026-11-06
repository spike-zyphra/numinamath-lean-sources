import Mathlib

theorem number_theory_13657 :
    ∑ᶠ p ∈ {p : ℕ | Nat.Prime p ∧ Nat.Prime (p ^ 2 + 20)}, p = 3 := by
  have h1 : {p : ℕ | Nat.Prime p ∧ Nat.Prime (p ^ 2 + 20)} = {3} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume Nat.Prime p ∧ Nat.Prime (p ^ 2 + 20), prove p = 3
      intro h
      rcases h with ⟨h1, h2⟩
      by_cases h3 : p ≤ 3
      · -- p ≤ 3
        interval_cases p <;> norm_num at h1 h2 ⊢ <;> tauto
      · -- Assume p > 3
        have h4 : p > 3 := by linarith
        have h5 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
          omega
        rcases h5 with (h5 | h5 | h5)
        · -- Case p ≡ 0 mod 3
          have h6 : p % 3 = 0 := h5
          have h7 : ¬ Nat.Prime p := by 
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
            all_goals linarith
          contradiction
        · -- Case p ≡ 1 mod 3
          have h8 : p % 3 = 1 := h5
          have h9 : (p ^ 2 + 20) % 3 = 0 := by
            have h10 : p ^ 2 % 3 = 1 := by
              have h11 : p % 3 = 1 := h8
              norm_num [Nat.pow_mod, h11]
            omega
          have h10 : ¬ Nat.Prime (p ^ 2 + 20) := by 
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p ^ 2 + 20 by omega)
            all_goals nlinarith
          contradiction
        · -- Case p ≡ 2 mod 3
          have h12 : p % 3 = 2 := h5
          have h9 : (p ^ 2 + 20) % 3 = 0 := by
            have h10 : p ^ 2 % 3 = 1 := by
              have h11 : p % 3 = 2 := h12
              norm_num [Nat.pow_mod, h11]
            omega
          have h10 : ¬ Nat.Prime (p ^ 2 + 20) := by 
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p ^ 2 + 20 by omega)
            all_goals nlinarith
          contradiction
    · -- Assume p = 3, prove Nat.Prime p ∧ Nat.Prime (p ^ 2 + 20)
      intro h
      rw [h]
      constructor
      · norm_num
      · norm_num
  rw [h1]
  rw [finsum_mem_singleton]
  all_goals norm_num