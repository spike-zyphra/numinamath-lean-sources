import Mathlib

theorem number_theory_82297 : ¬∃ m n, m^2 - n^2 = 2010 := by
  rintro ⟨m, n, h_eq⟩
  -- First establish the possible residues of m^2 and n^2 modulo 4
  have h1 : m^2 % 4 = 0 ∨ m^2 % 4 = 1 := by
    have h1 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1) <;> 
      simp [pow_two, Nat.mul_mod, h1] <;> omega

  have h2 : n^2 % 4 = 0 ∨ n^2 % 4 = 1 := by
    have h2 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
      omega
    rcases h2 with (h2 | h2 | h2 | h2) <;> 
      simp [pow_two, Nat.mul_mod, h2] <;> omega

  -- Now we have equations for m^2 and n^2 modulo 4
  -- m^2 ≡ 0 or 1 (mod 4) and n^2 ≡ 0 or 1 (mod 4)
  omega