import Mathlib

theorem number_theory_274838 :
    {n : ℕ | (∃ k : ℕ, n = k^2) ∧ (Nat.digits 10 n).length = 6 ∧
      (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) = n} = {698896} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First direction: if n in the set, then n = 698896
    rintro ⟨⟨k, rfl⟩, hk1, hk2⟩
    have h1 : k ≤ 999 := by
      by_contra h
      push_neg at h
      have h2 : k^2 ≥ 1000000 := by
        have : k ≥ 1000 := by omega
        nlinarith
      have h3 : (Nat.digits 10 (k^2)).length > 6 := by
        have h4 : k^2 ≥ 1000000 := h2
        have h5 : (Nat.digits 10 (k^2)).length > 6 := by
          have h6 : Nat.log 10 (k^2) ≥ 6 := by
            apply Nat.le_log_of_pow_le (by norm_num) h4
          have h7 : (Nat.digits 10 (k^2)).length = Nat.log 10 (k^2) + 1 := by
            rw [Nat.digits_len]
            all_goals
              omega
          omega
        omega
      omega
    have h2 : k ≥ 317 := by
      by_contra h
      push_neg at h
      have h3 : k ≤ 316 := by omega
      have h4 : (Nat.digits 10 (k^2)).length < 6 := by
        have h1 : k ≤ 316 := h3
        have h2 : k ^ 2 < 100000 := by
          nlinarith [show k ≤ 316 by omega]
        by_cases hk0 : k = 0
        · -- Case k = 0
          rw [hk0]
          norm_num
        · -- Case k > 0
          have hk00 : k > 0 := by
            by_contra h0
            push_neg at h0
            have : k = 0 := by omega
            contradiction
          have h3 : k ^ 2 > 0 := by
            nlinarith [hk00]
          have h5 : (Nat.digits 10 (k^2)).length ≤ 5 := by
            have h6 : k ^ 2 < 100000 := h2
            have h10 : Nat.log 10 (k ^ 2) ≤ 4 := by
              have h9 : k ^ 2 < 100000 := h2
              have h11 : Nat.log 10 (k ^ 2) < 5 := by
                apply Nat.log_lt_of_lt_pow
                all_goals
                  omega
              omega
            have h11 : (Nat.digits 10 (k ^ 2)).length = Nat.log 10 (k ^ 2) + 1 := by
              rw [Nat.digits_len]
              all_goals
                omega
            rw [h11]
            omega
          omega
      omega
    interval_cases k <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at hk1 hk2 ⊢
  · -- Second direction: if n = 698896, then n is in the set
    intro h
    rw [h]
    constructor
    · -- Show that 698896 is a perfect square
      use 836
      all_goals
        norm_num
    constructor
    · -- Show that the length of 698896 is 6
      norm_num
    · -- Show that 698896 equals its digit reverse
      norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]