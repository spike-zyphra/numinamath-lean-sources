import Mathlib

theorem algebra_11481 (a b c d : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hd : d.Prime) (h : a < b ∧ b < c ∧ c < d) (h1 : a > 5) (h2 : b = a + 6) (h3 : c = b + 6)
    (h4 : d = c + 6) :
    a % 10 = 1 := by
  have h51 : a % 2 = 1 := by
    by_contra h
    push_neg at h
    have h62 : ¬ a.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ a by omega)
      all_goals omega
    tauto
  by_cases h05 : a % 5 = 0
  · -- Assume a : divisible by 5
    have h62 : ¬ a.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ a by omega)
      all_goals omega
    tauto
  have h52 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
    omega
  rcases h52 with (h52 | h52 | h52 | h52)
  · -- Assume a ≡ 1 [MOD 5]
    have h85 : a % 10 = 1 := by
      have h0 : a % 10 = 1 ∨ a % 10 = 3  ∨ a % 10 = 7  ∨ a % 10 = 9 := by
        omega
      rcases h0 with (h0 | h0 | h0 | h0)
      · 
        omega 
      · 
        have h7 : a % 5 = 3 := by 
          omega 
        omega 
      · 
        have h7 : a % 5 = 2 := by 
          omega 
        omega 
      · 
        have h7 : a % 5 = 4 := by 
          omega 
        omega
    exact h85 
  · -- Assume a ≡ 2 [MOD 5] 
    -- In this case, we will show that d is divisible by 5 (so d is composite)
    have h42 : d % 5 = 0 := by 
      rw [h4, h3, h2]
      simp [Nat.add_mod, h52]
    have h25 : 5 ∣ d := by 
      omega
    have h31 : ¬ d.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt h25 
      all_goals 
        linarith [hd, h1]
    tauto 
  · -- Assume a ≡ 3 [MOD 5]
    -- In this case, we will show that c is divisible by 5 (so c is composite)
    have h423 : c % 5 = 0 := by 
      simp [h3, h2, Nat.add_mod, h52]
    have h25 : 5 ∣ c := by 
      omega
    have h31 : ¬ c.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt h25 
      all_goals 
        linarith [hc, h1]
    tauto 
  · -- Assume a ≡ 4 [MOD 5]
    -- In this case, we will show that b is divisible by 5 (so b is composite)
    have h429 : b % 5 = 0 := by 
      simp [h2, Nat.add_mod, h52] 
    have h25 : 5 ∣ b := by 
      omega 
    have h31 : ¬ b.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt h25 
      all_goals 
        linarith [hb, h1]
    tauto