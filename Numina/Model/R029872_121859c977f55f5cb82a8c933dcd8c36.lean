import Mathlib

  theorem number_theory_50136 : ¬∃ n : ℤ, n^3 = 10^150 + 5 * 10^100 + 1 := by 
  rintro ⟨n, hn⟩
  have h1 : n^3 % 9 = 0 ∨ n^3 % 9 = 1 ∨ n^3 % 9 = 8 := by
    have h2 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by
      omega
    rcases h2 with (h | h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
  
  -- Determine the value of $N \bmod 9| 
  -- Calculate (N : 10^100 and 10^100)
  have h2 : (10^150 + 5 * 10^100 + 1 : ℤ) % 9 = 7 := by
    norm_num
  
  -- Because n^3 = N, so n^3 ≡ 7 (mod 9).
  have h3 : (n^3 : ℤ) % 9 = 7 := by 
    omega
  
  -- h1 : $n \bmod 9$ can only be 0, 1, 8, so to have it be 7 is impossible.
  omega