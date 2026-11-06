import Mathlib

theorem number_theory_4789 (n : ℤ) (h₀ : n > 0) : 42 ∣ n^7 - n := by
  -- We need to prove that 42 divides n^7 - n
  -- We'll approach this by showing congruences modulo 2, 3, and 7
  -- First, prove that n^7 ≡ n (mod 2)
  have h1 : n^7 % 2 = n % 2 := by
    have h2 : n % 2 = 0 ∨ n % 2 = 1 := by
      omega
    rcases h2 with (h2 | h2)
    ·
      simp [pow_succ, Int.mul_emod, Int.add_emod, h2]
    ·
      simp [pow_succ, Int.mul_emod, Int.add_emod, h2]
  -- Next, prove that n^7 ≡ n (mod 3)
  have h3 : n^7 % 3 = n % 3 := by
    have h4 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h4 with (h4 | h4 | h4)
    ·
      simp [pow_succ, Int.mul_emod, Int.add_emod, h4]
    ·
      simp [pow_succ, Int.mul_emod, Int.add_emod, h4]
    ·
      simp [pow_succ, Int.mul_emod, Int.add_emod, h4]
  -- Next, prove that n^7 ≡ n (mod 7)
  have h7 : n^7 % 7 = n % 7 := by
    have h8 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
      omega
    rcases h8 with (h8 | h8 | h8 | h8 | h8 | h8 | h8)
    ·
      simp [pow_succ, Int.mul_emod, Int.add_emod, h8]
    ·
      simp [pow_succ, Int.mul_emod, Int.add_emod, h8]
    ·
      simp [pow_succ, Int.mul_emod, Int.add_emod, h8]
    ·
      simp [pow_succ, Int.mul_emod, Int.add_emod, h8]
    ·
      simp [pow_succ, Int.mul_emod, Int.add_emod, h8]
    ·
      simp [pow_succ, Int.mul_emod, Int.add_emod, h8]
    ·
      simp [pow_succ, Int.mul_emod, Int.add_emod, h8]
  -- Now, using these congruences, apply the Chinese Remainder Theorem
  omega