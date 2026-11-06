import Mathlib

--Determine whether there is a natural number $$n$$ for which $$8^n + 47$$ is prime.

theorem Number_Theory_604274: ∀ n : ℕ, ∃ t : ℕ, 1 < t ∧ t < 8 ^ n + 47 ∧ (8 ^ n + 47) % t = 0 := by 
  intro n
  -- cases n into 3 conditions
  have n1: n % 2 = 0 ∨ n % 4 = 1 ∨ n % 4 = 3 := by
    match h: n % 4 with
    | 0 =>
      left
      apply Nat.mod_eq_zero_of_dvd
      apply Nat.dvd_trans (by decide : 2 ∣ 4)
      rw [Nat.dvd_iff_mod_eq_zero, h]
    | 1 =>
      right
      left
      rfl
    | 2 =>
      left
      rw [← Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4), h]      
    | 3 =>
      right
      right
      rfl
    | k + 4 =>
      have h_lt : n % 4 < 4 := Nat.mod_lt n (by decide : 0 < 4)
      rw [h] at h_lt
      nlinarith
  -- suppose n is even
  cases n1 with
  | inl h1 => 
    have h_even : ∃ k, n = 2 * k := by exact ⟨n / 2, by omega⟩
    have k1: (8 ^ n ) % 3 = 1 :=by 
      obtain ⟨k, hk⟩ := h_even
      rw [hk, pow_mul]
      have h64_mod3 : 64 % 3 = 1 := by rfl
      have k2: 64 ^ k % 3 = 1 := 
        calc 64 ^ k % 3
          _ = (64 % 3) ^ k % 3 := by rw [Nat.pow_mod]
          _ = 1 ^ k % 3         := by rw [h64_mod3]  
          _ = 1 % 3             := by rw [one_pow]   
          _ = 1                 := by decide 
      exact k2
    have m1: (47 : ℕ) % 3 = 2 := by norm_num
    have m2: ((8 ^ n + 47) % 3 = 0) :=by omega
    have m3: (8 ^ n + 47) > 3 := 
      calc 8 ^ n + 47 
        _ ≥ 8 ^ 0 + 47 := by apply Nat.add_le_add_right; apply Nat.pow_le_pow_of_le_right (by decide) (Nat.zero_le n)
        _ = 48 := by rfl
        _ > 3 := by decide
    have m4: 3 > 1:= by trivial
    use 3
  -- suppose n mod 4 equals 1 and n mod 4 equals 3
  | inr h1 => cases h1 with
    | inl h1 => 
      have h2: ∃ k, n = 4 * k + 1 := by exact ⟨(n - 1)/ 4, by omega ⟩
      have h_mod5: 8 ^ 4 % 5 = 1 := by rfl 
      obtain ⟨k, hk⟩ := h2      
      have h1_mod5: (8 ^ 4) ^ k % 5 = 1 := 
        calc (8 ^ 4) ^ k % 5 = (8 ^ 4 % 5 ) ^ k % 5 := by rw [Nat.pow_mod]
                          _ = 1 ^ k % 5              := by rw [h_mod5]
                          _ = 1 % 5                  := by rw [one_pow]
                          _ = 1                      := by decide
      have h3: (8 ^ (4 * k + 1)) % 5 = 3 :=
        calc (8 ^ (4 * k + 1)) % 5 = (8 ^ 4) ^ k * 8 % 5 := by rw [pow_add, ← pow_mul, pow_one]
                                      _ = ((8 ^ 4) ^ k % 5) * (8 % 5) % 5    := by rw[Nat.mul_mod]
                                      _ = (1 % 5) * 8 % 5                    := by rw[h1_mod5]
                                      _ = 3 % 5                              := by rfl
                                      _ = 3                                  := by rfl
      have k1: (8 ^ n) % 5 = 3 :=by rw [← hk] at h3 ;exact h3
      have m1: (47 : ℕ) % 5 = 2 := by norm_num
      have m2: ((8 ^ n + 47) % 5 = 0):= by omega
      have m3: (8 ^ n + 47) > 5 :=         
        calc _ ≥ 8 ^ 0 + 47 := by apply Nat.add_le_add_right; apply Nat.pow_le_pow_of_le_right (by decide) (Nat.zero_le n)
        _ = 48 := by rfl
        _ > 5 := by decide
      have m4: 5 > 1 := by trivial
      use 5
    | inr h1 => 
      have h2: ∃ k, n = 4 * k + 3 := by exact ⟨(n - 1)/ 4, by omega⟩
      have h_mod13: 8 ^ 4 % 13 = 1 := by rfl 
      obtain ⟨k, hk⟩ := h2      
      have h1_mod13: (8 ^ 4) ^ k % 13 = 1 := 
        calc (8 ^ 4) ^ k % 13 = (8 ^ 4 % 13 ) ^ k % 13 := by rw [Nat.pow_mod]
                          _ = 1 ^ k % 13              := by rw [h_mod13]
                          _ = 1 % 13                  := by rw [one_pow]
                          _ = 1                      := by decide
      have h3: (8 ^ (4 * k + 3)) % 13 = 5 :=
        calc (8 ^ (4 * k + 3)) % 13 =  (8 ^ (4 * k) * 8 ^ 3) % 13 := by rw [pow_add]
                                      _ = ((8 ^ 4) ^ k % 13) * (8 ^ 3 % 13) % 13 := by rw [← pow_mul];rw[Nat.mul_mod]
                                      _ = (1 % 13) * (8 ^ 3 % 13) % 13              := by rw[h1_mod13]
                                      _ = 5 % 13                              := by rfl
                                      _ = 5                                  := by rfl
      have k1: (8 ^ n) % 13 = 5 :=by rw [← hk] at h3 ;exact h3
      have m1: (47 : ℕ) % 13 = 8 := by norm_num
      have m2: ((8 ^ n + 47) % 13 = 0):= by omega
      have m3: (8 ^ n + 47) > 13 :=         
        calc _ ≥ 8 ^ 0 + 47 := by apply Nat.add_le_add_right; apply Nat.pow_le_pow_of_le_right (by decide) (Nat.zero_le n)
        _ = 48 := by rfl
        _ > 13 := by decide
      have m4: 13 > 1 := by trivial
      use 13