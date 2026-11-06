import Mathlib

theorem number_theory_184570 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : p > 3) (h' : q > 3) :
    24 ∣ (p ^ 2 - q ^ 2) := by
  have hp1 : p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 ∨ p % 24 = 13 ∨ p % 24 = 17 ∨ p % 24 = 19 ∨ p % 24 = 23 := by
    by_contra h1
    push_neg at h1
    have h1 : p % 2 = 0 ∨ p % 3 = 0 := by
      omega
    by_cases h2 : p % 2 = 0
    · -- p is even, not prime
      have h3 : ¬ p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
        all_goals omega
      contradiction
    · -- p not even, so divisible by 3
      have h3 : p % 3 = 0 := by
        tauto
      have h4 : 3 ∣ p := by
        omega
      have h5 : ¬ p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega
      contradiction

  have hp2 : p ^ 2 % 24 = 1 := by
    rcases hp1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
      norm_num [Nat.pow_mod, h1, Nat.mul_mod] 
  have hq1 : q % 24 = 1 ∨ q % 24 = 5 ∨ q % 24 = 7 ∨ q % 24 = 11 ∨ q % 24 = 13 ∨ q % 24 = 17 ∨ q % 24 = 19 ∨ q % 24 = 23 := by
    by_contra h1
    push_neg at h1
    have h1 : q % 2 = 0 ∨ q % 3 = 0 := by
      omega
    by_cases h2 : q % 2 = 0
    · -- q is even, not prime
      have h3 : ¬ q.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
        all_goals omega
      contradiction
    · -- q not even, so divisible by 3
      have h3 : q % 3 = 0 := by
        tauto
      have h4 : 3 ∣ q := by
        omega
      have h5 : ¬ q.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega)
        all_goals omega
      contradiction

  have hq2 : q ^ 2 % 24 = 1 := by
    rcases hq1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
      norm_num [Nat.pow_mod, h1, Nat.mul_mod] 
  have h1 : (p ^ 2 : ℕ) % 24 = 1 := by
    omega
  have h2 : (q ^ 2 : ℕ) % 24 = 1 := by
    omega
  have h3 : (p ^ 2 : ℕ) % 24 = (q ^ 2 : ℕ) % 24 := by
    omega
  have h4 : 24 ∣ (p ^ 2 - q ^ 2) := by
    omega
  exact h4