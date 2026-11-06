import Mathlib

theorem number_theory_97193 (p : ℕ) (hp : p.Prime) (hp1 : 5 ≤ p) : 24 ∣ (p ^ 2 - 1) := by
  have h1 : p % 2 ≠ 0 := by
    by_contra h
    have : ¬ p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals linarith
    contradiction

  have h2 : p % 3 ≠ 0 := by
    by_contra h
    have : 3 ∣ p := by 
      omega
    have : ¬ p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by assumption)
      all_goals linarith
    contradiction

  have h3 : (p ^ 2) % 8 = 1 := by
    have h4 : p % 2 ≠ 0 := h1
    have h5 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
      omega
    rcases h5 with (h | h | h | h) <;> simp [Nat.pow_mod, h]

  have h6 : (p ^ 2) % 3 = 1 := by
    have h7 : p % 3 ≠ 0 := h2
    have h8 : p % 3 = 1 ∨ p % 3 = 2 := by 
      omega
    rcases h8 with (h | h) <;> simp [Nat.pow_mod, h]

  -- Now, to prove $24$ divides $p^2 - 1$ we show $p^2 \equiv 1 \pmod{24}$.
  have h7 : (p ^ 2) % 24 = 1 := by
    omega

  -- Therefore $24$ divides $p^2 - 1$.
  exact Nat.dvd_of_mod_eq_zero (show (p ^ 2 - 1) % 24 = 0 by 
    omega
  )