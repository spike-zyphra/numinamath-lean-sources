import Mathlib

theorem number_theory_607604 :
    Set.Finite {p | p.Prime ∧ ∃ n, p = n^3 + 2 * n + 3} := by
  have h4 : {p | p.Prime ∧ ∃ n, p = n^3 + 2 * n + 3} = {3} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume p is in the set.
      intro h
      rcases h with ⟨h_prime, ⟨n, rfl⟩⟩
      by_cases hn : n > 0
      · -- Case n > 0.
        have h5 : (n ^ 3 + 2 * n + 3) % 3 = 0 := by
          have h1 : ∀ (n : ℕ), (n ^ 3 + 2 * n + 3) % 3 = 0 := by
            intro n
            have h11 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
            rcases h11 with (h | h | h)
            · -- Case n ≡ 0 (mod 3)
              simp [h, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
            · -- Case n ≡ 1 (mod 3)
              simp [h, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
            · -- Case n ≡ 2 (mod 3)
              simp [h, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
          specialize h1 n 
          simpa using h1
        have h7 : ¬ Nat.Prime (n ^ 3 + 2 * n + 3) := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (n ^ 3 + 2 * n + 3) by omega) 
          all_goals
          -- Show that 3 < n^3 + 2n + 3 when n > 0
          have h11 : n ^ 3 + 2 * n + 3 > 3 := by
            have h2 : n ≥ 1 := by omega
            have h3 : n ^ 3 ≥ 1 := by
              have h4 : n ^ 3 ≥ 1 ^ 3 := by
                apply Nat.pow_le_pow_of_le_left
                omega
              norm_num at h4 ⊢
              linarith
            linarith
          all_goals
          omega
        contradiction
      · -- Case n ≤ 0 (so n = 0).
        have hn0 : n = 0 := by
          omega
        rw [hn0]
        all_goals
        norm_num at *
    · -- Assume p = 3.
      intro hp
      rw [hp]
      constructor
      · -- Show 3 is prime.
        norm_num
      · -- Show ∃ n, 3 = n^3 + 2n + 3.
        use 0
        all_goals
        norm_num
  rw [h4]
  simp