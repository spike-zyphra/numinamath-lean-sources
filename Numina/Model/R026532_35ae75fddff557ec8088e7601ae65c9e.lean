import Mathlib

theorem number_theory_191753 (n : ℕ) :
    42 ∣ n^3 * (n^6 - 1) := by
-- We need to prove $42$ divides $n^{3}(n^{6}-1)$.
-- This is equivalent to proving divisibility by 2, 3, and 7
  -- prove the expression can be divided by 2
  have h1 : n ^ 3 * (n ^ 6 - 1) % 2 = 0 := by
    have h1 : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases h1 with (h1 | h1)
    · -- when n is even
      have h2 : n % 2 = 0 := h1
      simp [Nat.mul_mod, Nat.pow_mod, h2]
      all_goals omega
    · -- when n is odd
      have h2 : n % 2 = 1 := h1
      have h2' : n ^ 6 % 2 = 1 := by
        -- We know that if n is odd, then n^6 is odd.
        -- So n^6 ≡ 1 (mod 2).
        simp [Nat.pow_mod, h2]
        all_goals omega
      have h5 : (n ^ 6 - 1) % 2 = 0 := by 
        omega
      simp [Nat.mul_mod, h5]
      all_goals omega

  -- prove the expression can be divided by 3
  have h2 : n ^ 3 * (n ^ 6 - 1) % 3 = 0 := by
    have h111 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h111 with (h111 | h111 | h111)
    · -- when n is divisible by 3
      simp [Nat.mul_mod, Nat.pow_mod, h111]
      all_goals omega
    · -- when n ≡ 1 (mod 3)
      have h1111 : n % 3 = 1 := h111
      -- We know from Fermat's Little Theorem, or basic modular arithmetic, that n^6 ≡ 1 (mod 3).
      -- Specifically, if n ≡ 1 (mod 3), then n^6 ≡ (1)^6 ≡ 1 (mod 3).
      have h2222 : n ^ 6 % 3 = 1 := by
        simp [Nat.pow_mod, h1111]
        all_goals omega
      have h3333 : (n ^ 6 - 1) % 3 = 0 := by
        omega
      simp [Nat.mul_mod, h2222, h3333]
      all_goals omega
    · -- when n ≡ 2 (mod 3)
      have h1112 : n % 3 = 2 := h111
      -- We know by Fermat's Little Theorem, n^6 ≡1 (mod 3).
      -- Specifically, if n ≡2 (mod 3), n^6 ≡ (2^2)^3 ≡ 1^3 ≡1 (mod 3).
      have h22222 : n ^ 6 % 3 = 1 := by
        simp [Nat.pow_mod, h1112]
        all_goals 
          omega
      have h3336 : (n ^ 6 - 1) % 3 = 0 := by
        omega
      simp [Nat.mul_mod, h22222, h3336]
      all_goals omega

  -- prove the expression can be divided by 7
  have h3 : n ^ 3 * (n ^ 6 - 1) % 7 = 0 := by
    have h11111 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by omega
    rcases h11111 with (h11111 | h11111 | h11111 | h11111 | h11111 | h11111 | h11111)
    · -- when n is divisible by 7
      simp [Nat.mul_mod, Nat.pow_mod, h11111]
      all_goals omega
    · -- when n % 7 = 1
      have h111111 : n % 7 = 1 := h11111
      -- We know by Fermat's Little Theorem, n^6 ≡ 1 (mod 7).
      -- Specifically, if n ≡1 (mod 7), n^6 ≡1 (mod 7).
      have h222222 : n ^ 6 % 7 = 1 := by
        simp [Nat.pow_mod, h111111]
        all_goals 
          omega
      -- Therefore we know n^6 - 1 ≡0 (mod 7).
      have h333333 : (n ^ 6 - 1) % 7 = 0 := by
        omega
      -- Now we can show the product is divisible by 7.
      simp [Nat.mul_mod, h222222, h333333, h111111]
      all_goals 
        omega
    · -- when n % 7 = 2
      have h11111111 : n % 7 = 2 := h11111
      -- We know by Fermat's Little Theorem, n^6 ≡1 (mod 7).
      -- Specifically, if n ≡2 (mod 7), n^6 = (2^6) = 64 ≡ 1 (mod 7).
      have h2222222 : n ^ 6 % 7 = 1 := by
        simp [Nat.pow_mod, h11111111]
        all_goals 
          omega
      -- Therefore we know n^6 - 1 ≡0 (mod 7).
      have h333334 : (n ^ 6 - 1) % 7 = 0 := by
        omega
      -- Now we can show the product is divisible by 7.
      simp [Nat.mul_mod, h2222222, h333334, h11111111]
      all_goals 
        omega
    · -- when n % 7 = 3
      have h1111111111 : n % 7 = 3 := h11111
      -- We know by Fermat's Little Theorem, n^6 ≡1 (mod 7).
      -- Specifically, if n ≡3 (mod 7), n^6 = (3^6) = 729 ≡ 1 (mod 7).
      have h2222224 : n ^ 6 % 7 = 1 := by
        simp [Nat.pow_mod, h1111111111]
        all_goals 
          omega
      -- Therefore we know n^6 - 1 ≡0 (mod 7).
      have h333338 : (n ^ 6 - 1) % 7 = 0 := by
        omega
      -- Now we can show the product is divisible by 7.
      simp [Nat.mul_mod, h2222224, h333338, h1111111111]
      all_goals 
        omega
    · -- when n % 7 = 4
      have h1111111112 : n % 7 = 4 := h11111
      -- We know by Fermat's Little Theorem, n^6 ≡1 (mod 7).
      -- Specifically, if n ≡4 (mod 7), n^6 = (4^6) = 4096 ≡ 1 (mod 7).
      have h22222232 : n ^ 6 % 7 = 1 := by
        simp [Nat.pow_mod, h1111111112]
        all_goals 
          omega
      -- Therefore we know n^6 - 1 ≡0 (mod 7).
      have h3333362 : (n ^ 6 - 1) % 7 = 0 := by
        omega
      -- Now we can show the product is divisible by 7.
      simp [Nat.mul_mod, h22222232, h3333362, h1111111112]
      all_goals 
        omega
    · -- when n % 7 = 5
      have h1111111131 : n % 7 = 5 := h11111
      -- We know by Fermat's Little Theorem, n^6 ≡1 (mod 7).
      -- Specifically, if n ≡5 (mod 7), n^6 = (5^6) = 15625 ≡ 1 (mod 7).
      have h22222264 : n ^ 6 % 7 = 1 := by
        simp [Nat.pow_mod, h1111111131]
        all_goals 
          omega
      -- Therefore we know n^6 - 1 ≡0 (mod 7).
      have h33333197686535 : (n ^ 6 - 1) % 7 = 0 := by
        omega
      -- Now we can show the product is divisible by 7.
      simp [Nat.mul_mod, h22222264, h33333197686535, h1111111131]
      all_goals 
        omega
    · -- when n % 7 = 6
      have h1111111111118 : n % 7 = 6 := h11111
      -- We know by Fermat's Little Theorem, n^6 ≡1 (mod 7).
      -- Specifically, if n ≡6 (mod 7), n^6 = (6^6) = 46656 ≡ 1 (mod 7).
      have h2222222222211 : n ^ 6 % 7 = 1 := by
        simp [Nat.pow_mod, h1111111111118]
        all_goals 
          omega
      -- Therefore we know n^6 - 1 ≡0 (mod 7).
      have h3334 : (n ^ 6 - 1) % 7 = 0 := by
        omega
      -- Now we can show the product is divisible by 7.
      simp [Nat.mul_mod, h2222222222211, h3334, h1111111111118]
      all_goals 
        omega

  -- combine the results
  omega