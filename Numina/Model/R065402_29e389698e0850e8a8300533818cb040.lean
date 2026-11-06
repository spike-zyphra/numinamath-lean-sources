import Mathlib

theorem number_theory_297685 (p : ℕ) (hp : Nat.Prime p) (h : 3 < p) :
    p^2 ≡ 1 [MOD 24] := by 
  have h1 : p % 2 ≠ 0 := by
    by_contra h1
    have h2 : ¬ Nat.Prime p := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals linarith
    contradiction

  have h2 : p % 3 ≠ 0 := by 
    by_contra h2
    have h3 : 3 ∣ p := by omega
    have h4 : ¬ Nat.Prime p := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
      all_goals linarith
    contradiction
  
  have h3 : p ^ 2 % 8 = 1 := by
    have h1 : p % 2 ≠ 0 := h1 
    have h4 : p % 2 = 1 := by 
      omega
    have : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by 
      omega
    rcases this with (h | h | h | h) <;> norm_num [Nat.pow_mod, h] at *
  
  have h4 : p ^ 2 % 3 = 1 := by 
    have h2 : p % 3 ≠ 0 := h2 
    have : p % 3 = 1 ∨ p % 3 = 2 := by 
      omega
    rcases this with (h | h) <;> norm_num [Nat.pow_mod, h] at *
  
  norm_num [Nat.ModEq] at *
  omega