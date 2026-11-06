import Mathlib


theorem number_theory_159148 (n m : ℕ) :
    2^n + 65 = m^2 ↔ (n = 4 ∧ m = 9) ∨ (n = 10 ∧ m = 33) := by
  constructor
  · -- Forward direction: If 2^n + 65 = m^2, then (n, m) is (4, 9) or (10, 33).
    intro h
    have h1 : n ≤ 10 := by
      by_contra h2
      push_neg at h2
      have h3 : m > 33 := by
        have h4 : 2 ^ n > 1024 := by
          have h5 : n > 10 := by linarith
          have h6 : 2 ^ n > 2 ^ 10 := by
            apply Nat.pow_lt_pow_right
            all_goals omega
          have h7 : 2 ^ 10 = 1024 := by norm_num
          linarith [h7, h6]
        have h8 : m ^ 2 > 1089 := by
          nlinarith [h, h4]
        have h9 : m > 33 := by
          nlinarith
        linarith
      -- Now for n > 10, show contradiction.
      have h2 : n % 2 = 0 := by
        by_contra h3
        have h3 : n % 2 = 1 := by
          omega
        have h5 : m ^ 2 % 5 = 0 ∨ m ^ 2 % 5 = 1 ∨ m ^ 2 % 5 = 4 := by
          have h1 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by
            omega
          rcases h1 with (h | h | h | h | h) <;> simp [pow_two, Nat.mul_mod, h]
        have h6 : (2 ^ n + 65) % 5 = 2 ∨ (2 ^ n + 65) % 5 = 3 := by
          have h7 : n % 2 = 1 := h3
          have h8 : 2 ^ n % 5 = 2 ∨ 2 ^ n % 5 = 3 := by
            have h9 : ∀ k : ℕ, 2 ^ (2 * k + 1) % 5 = 2 ∨ 2 ^ (2 * k + 1) % 5 = 3 := by
              intro k
              induction k with
              | zero =>
                norm_num
              | succ k ih =>
                simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
                all_goals omega
            have h10 : ∃ k, n = 2 * k + 1 := by
              refine' ⟨(n - 1) / 2, by omega⟩
            rcases h10 with ⟨k, hk⟩
            rw [show n = 2 * k + 1 by linarith [hk]]
            apply h9 k
          omega
        -- Contradicts with h5
        have h7 : m ^ 2 % 5 = 2 ∨ m ^ 2 % 5 = 3 := by
          omega
        -- But this is invalid, because a square cannot be 2 or 3 modulo 5.
        omega
      -- So, n is even.
      have h9 : ∃ k, n = 2 * k := by
        refine' ⟨n / 2, by omega⟩
      rcases h9 with ⟨k, hk⟩
      have h10 : m ^ 2 = 4 ^ k + 65 := by
        have h11 : 2 ^ n = (4) ^ k := by
          rw [show n = 2 * k by linarith [hk]]
          have h13 : 2 ^ (2 * k) = (2 ^ 2) ^ k := by
            rw [←pow_mul]
          rw [h13]
          all_goals ring_nf
        nlinarith [h, h11]
      -- Now, for k > 5, show contradiction.
      have h14 : k ≤ 5 := by
        by_contra h15
        push_neg at h15
        have h15 : k > 5 := by linarith
        -- Now, need to show contradiction.
        -- We have $m^2 = 4^k + 65$.
        -- For k > 5, $4^k$ is divisible by 64. So $m^2 \equiv 1 \pmod{64}$.
        -- This is okay.
        have h77 : (m : ℤ) ^ 2 = (4 ^ k + 65 : ℤ) := by
          exact_mod_cast h10
        -- Now, we can use a theorem about difference of squares. Let's write $(m)^2 - (2^k)^2 = 65$.
        have h78 : (m : ℤ) ^ 2 - (2 ^ k : ℤ) ^ 2 = 65 := by
          have h79 : (4 ^ k : ℤ) = (2 ^ k : ℤ) ^ 2 := by
            have h81 : (4 ^ k : ℤ) = (2 ^ k : ℤ) ^ 2 := by
              have h82 : (4 : ℤ) = 2 ^ 2 := by norm_num
              rw [h82]
              rw [← pow_mul]
              all_goals ring
            linarith
          nlinarith [h77, h79]
        -- Now, factor the left side.
        have h79 : ((m : ℤ) - (2 ^ k : ℤ)) * ((m : ℤ) + (2 ^ k : ℤ)) = 65 := by
          nlinarith [h78]
        -- Now, find the possible pairs of integers.
        have h84 : ((m : ℤ) - (2 ^ k : ℤ)) ∣ 65 := by
          use ((m : ℤ) + (2 ^ k : ℤ))
          all_goals nlinarith
        -- Now, bound the divisor.
        have h85 : ((m : ℤ) - (2 ^ k : ℤ)) ≤ 65 := by
          exact Int.le_of_dvd (by norm_num) h84
        have h86 : ((m : ℤ) - (2 ^ k : ℤ)) ≥ -65 := by
          have h87 : -((m : ℤ) - (2 ^ k : ℤ)) ∣ 65 := by
            exact Int.neg_dvd.2 h84
          have h88 : -((m : ℤ) - (2 ^ k : ℤ)) ≤ 65 := by
            exact Int.le_of_dvd (by norm_num) h87
          linarith
        interval_cases h88 : (m : ℤ) - (2 ^ k : ℤ) <;> omega
      -- So now, k ≤ 5.
      interval_cases k <;> try { 
        norm_num at h10
        all_goals
          have h15 : m ≤ 33 := by
            nlinarith
          interval_cases m <;> omega
      }
    -- Now, n ≤ 10.
    interval_cases n <;> try { 
      norm_num at h 
      all_goals
        have h15 : m ≤ 33 := by
          nlinarith
        interval_cases m <;> omega 
    }
  · -- Backward direction: If (n, m) is (4, 9) or (10, 33), then 2^n + 65 = m^2.
    rintro (h | h)
    · -- Case (4, 9).
      rcases h with ⟨rfl, rfl⟩
      all_goals
        norm_num
    · -- Case (10, 33).
      rcases h with ⟨rfl, rfl⟩
      all_goals
        norm_num