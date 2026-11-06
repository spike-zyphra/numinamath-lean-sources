import Mathlib

theorem number_theory_231612 (p : ℕ) (hp : Nat.Prime p) (h : 3 < p) : 24 ∣ (p^2 - 1) := by
  have h1 : p % 2 ≠ 0 := by
    by_contra h1
    have h2 : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals linarith
    tauto

  -- Since p is a prime greater than 3, it's not divisible by 3
  have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
    have h3 : p % 3 ≠ 0 := by 
      by_contra h3
      have h4 : p % 3 = 0 := by omega
      have h5 : 3 ∣ p := by 
        omega
      have h6 : ¬Nat.Prime p := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals linarith 
      tauto 
    omega
  have h3 : p % 2 = 1 := by omega
  have h4 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    omega
  have h5 : (p ^ 2) % 8 = 1 := by
    rcases h4 with (h4 | h4 | h4 | h4) <;> simp [pow_two, Nat.mul_mod, h4] 
  have h6 : (p ^ 2) % 3 = 1 := by
    rcases h2 with (h2 | h2) <;> simp [pow_two, Nat.mul_mod, h2]
  have h7 : (p ^ 2 - 1) % 8 = 0 := by
    omega
  have h8 : (p ^ 2 - 1) % 3 = 0 := by
    omega
  omega