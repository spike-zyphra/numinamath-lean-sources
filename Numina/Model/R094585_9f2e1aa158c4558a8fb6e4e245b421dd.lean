import Mathlib

theorem number_theory_258371 (n : ℤ) (h₀ : ¬ 5 ∣ n) : 30 ∣ n^5 - n := by
  have h1 : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  have h3 : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    omega
  -- The idea is to prove that $n^5 \equiv n \pmod{2}$, $n^5 \equiv n \pmod{3}$, and $n^5 \equiv n \pmod{5}$.

  have h4 : n^5 % 2 = n % 2 := by 
    rcases h1 with (h | h)
    · 
      simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      <;> omega
    · 
      simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      <;> omega

  have h5 : n^5 % 3 = n % 3 := by
    rcases h2 with (h | h | h)
    · 
      simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      <;> omega
    · 
      simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      <;> omega
    · 
      simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      <;> omega

  have h6 : n^5 % 5 = n % 5 := by
    rcases h3 with (h | h | h | h)
    · 
      simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      <;> omega
    · 
      simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      <;> omega
    · 
      simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      <;> omega
    · 
      simp [h, pow_succ, Int.add_emod, Int.mul_emod]
      <;> omega
  -- Now we can prove $30 \mid n^5 -n$ using the Chinese Remainder Theorem.

  -- The fact follows from $n^5 \equiv n \pmod{2}$, $n^5 \equiv n \pmod{3}$, and $n^5 \equiv n \pmod{5}$.
  omega