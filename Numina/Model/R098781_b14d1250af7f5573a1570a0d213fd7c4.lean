import Mathlib

theorem number_theory_319139 (m n p : ℤ) :
    6 ∣ m + n + p → 6 ∣ m^3 + n^3 + p^3 := by 
  intro h
  -- Let's establish that m^3 ≡ m (mod 6)
  have h1 : m^3 % 6 = m % 6 := by 
    have h1 : m % 6 = 0 ∨ m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 3 ∨ m % 6 = 4 ∨ m % 6 = 5 := by 
      omega 
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h1] <;> omega 
  -- Similarly, let's establish that n^3 ≡ n (mod 6)
  have h2 : n^3 % 6 = n % 6 := by 
    have h2 : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by 
      omega 
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h2] <;> omega 
  -- And the same for p^3 ≡ p (mod 6)
  have h3 : p^3 % 6 = p % 6 := by 
    have h3 : p % 6 = 0 ∨ p % 6 = 1 ∨ p % 6 = 2 ∨ p % 6 = 3 ∨ p % 6 = 4 ∨ p % 6 = 5 := by 
      omega 
    rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h3] <;> omega 
  -- Now m^3 + n^3 + p^3 ≡ m + n + p (mod 6)
  -- Since 6 divides m + n + p, we have m + n + p ≡ 0 (mod 6)
  -- So m^3 + n^3 + p^3 ≡ 0 (mod 6), i.e., 6 divides m^3 + n^3 + p^3
  have h4 : (m^3 + n^3 + p^3) % 6 = 0 := by 
    simp [Int.add_emod, h1, h2, h3] at *
    omega 
  exact Int.dvd_of_emod_eq_zero h4