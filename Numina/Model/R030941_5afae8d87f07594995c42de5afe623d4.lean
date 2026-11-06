import Mathlib

theorem algebra_15972 :
    {n : ℕ | n % 10 = 3 ∧ (∃ p q, n = p - q ∧ p.Prime ∧ q.Prime)}.encard = 1 := by
  have h : {n : ℕ | n % 10 = 3 ∧ (∃ p q, n = p - q ∧ p.Prime ∧ q.Prime)} = {3} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume n in left side
      rintro ⟨h1, ⟨p, q, h2, hp, hq⟩⟩
      by_cases h3 : n > 3
      · -- Assume n > 3. Show contradiction
        have h4 : n % 10 = 3 := h1
        have h5 : p = q + n := by
          omega
        by_cases h6 : q % 2 = 1
        · -- If q is odd
          have h7 : q % 2 = 1 := h6
          have h8 : p % 2 = 0 := by
            omega
          have h9 : p > 2 := by
            omega
          have h11 : ¬p.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
            all_goals omega
          contradiction
        · -- If q is even
          have h6 : q % 2 = 0 := by
            omega
          have h7 : q = 2 := by
            by_cases h8 : q > 2
            · -- Assume q > 2
              have h9 : q % 2 = 0 := h6
              have h10 : q > 2 := h8
              have h11 : ¬q.Prime := by
                apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
                all_goals omega
              contradiction
            · -- Assume q ≤ 2
              interval_cases q <;> norm_num at *
          rw [h7] at h5
          have h8 : p = 2 + n := by
            omega
          have h9 : p % 5 = 0 := by
            omega
          have h10 : p > 5 := by
            omega
          have h11 : ¬p.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega)
            all_goals omega
          contradiction
      · -- Assume n ≤ 3
        interval_cases n <;> norm_num at *
        <;> omega
    · -- Now prove the reverse
      intro h_eq3
      rw [h_eq3]
      constructor
      · -- Show 3 % 10 = 3
        norm_num
      · -- Show ∃ p q, 3 = p - q ∧ p.Prime ∧ q.Prime
        use 5, 2
        all_goals norm_num
  rw [h]
  simp [Set.encard_singleton]