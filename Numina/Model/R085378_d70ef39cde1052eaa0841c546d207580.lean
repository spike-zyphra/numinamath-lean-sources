import Mathlib

theorem number_theory_48855 (p : ℕ) (hp : Nat.Prime p) (h : 3 < p) :
    (p ^ 2) % 12 = 1 := by
  have h1 : p % 3 ≠ 0 := by 
    by_contra h2
    have h3 : p ≠ 3 := by linarith
    have h4 : ¬ Nat.Prime p := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
      all_goals 
        linarith
    contradiction 
  have h2 : p % 2 ≠ 0 := by 
    by_contra h4
    have h5 : p ≠ 2 := by linarith
    have h6 : ¬ Nat.Prime p := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals 
        linarith
    contradiction 
  have h3 : p % 4 = 1 ∨ p % 4 = 3 := by 
    omega 
  have h4 : p % 3 = 1 ∨ p % 3 = 2 := by 
    omega 
  have h5 : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by 
    omega 
  rcases h5 with (h5 | h5 | h5 | h5)
  · -- case p ≡ 1
    simp [pow_two, Nat.mul_mod, h5]
    all_goals 
      omega
  · -- case p ≡ 5
    simp [pow_two, Nat.mul_mod, h5]
    all_goals 
      omega
  · -- case p ≡ 7
    simp [pow_two, Nat.mul_mod, h5]
    all_goals 
      omega
  · -- case p ≡ 11
    simp [pow_two, Nat.mul_mod, h5]
    all_goals 
      omega