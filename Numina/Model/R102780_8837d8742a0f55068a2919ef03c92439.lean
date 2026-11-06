import Mathlib

theorem number_theory_110047 (P : ℕ) (hP : Nat.Prime P) (hP1 : P > 3) :
    P^2 ≡ 1 [MOD 24] := by
  have h1 : P % 2 ≠ 0 := by
    by_contra h
    have h2 : ¬ Nat.Prime P := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ P by omega)
      all_goals omega
    contradiction

  have h3 : P % 3 ≠ 0 := by
    by_contra h
    have h4 : ¬ Nat.Prime P := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ P by omega)
      all_goals omega
    contradiction

  -- We need to compute possible residues of $P$ modulo 24 given $P$ is odd and not divisible by 3
  have h4 : P % 24 = 1 ∨ P % 24 = 5 ∨ P % 24 = 7 ∨ P % 24 = 11 ∨ P % 24 = 13 ∨ P % 24 = 17 ∨ P % 24 = 19 ∨ P % 24 = 23 := by 
    have h11 : P % 2 ≠ 0 := h1
    have h12 : P % 3 ≠ 0 := h3
    omega

  -- Now we compute $P^2$ for each possible residue
  rcases h4 with (h | h | h | h | h | h | h | h) <;> simp [Nat.ModEq, Nat.pow_mod, h]
  <;> omega