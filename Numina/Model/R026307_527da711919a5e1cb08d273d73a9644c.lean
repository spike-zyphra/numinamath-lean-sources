import Mathlib

theorem number_theory_156102 (p q r d : ℕ) (hpqr : p.Prime ∧ q.Prime ∧ r.Prime)
    (hqr : q - p = d) (hpr : r - q = d) (h : p > 3) (h' : q > 3) (h'' : r > 3) :
    6 ∣ d := by 
  rcases hpqr with ⟨hp, hq, hr⟩
  have h1 : p % 2 = 1 := by
    by_contra h1
    push_neg at h1
    have : ¬p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals omega
    contradiction
  have h2 : q % 2 = 1 := by 
    by_contra h2
    push_neg at h2 
    have : ¬q.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
      all_goals omega
    contradiction
  have h3 : r % 2 = 1 := by 
    by_contra h3 
    push_neg at h3
    have : ¬r.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ r by omega)
      all_goals omega
    contradiction
  have h4 : p % 3 = 1 ∨ p % 3 = 2 := by 
    by_contra h4 
    push_neg at h4 
    have h5 : p % 3 = 0 := by omega 
    have : ¬p.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
      all_goals omega 
    contradiction
  have h5 : q % 3 = 1 ∨ q % 3 = 2 := by 
    by_contra h5 
    push_neg at h5 
    have h6 : q % 3 = 0 := by omega 
    have : ¬q.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega)
      all_goals omega 
    contradiction
  have h6 : r % 3 = 1 ∨ r % 3 = 2 := by 
    by_contra h6 
    push_neg at h6 
    have h7 : r % 3 = 0 := by omega 
    have : ¬r.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ r by omega)
      all_goals omega 
    contradiction
  have h7 : d % 2 = 0 := by
    omega
  have h8 : d % 3 = 0 := by
    omega
  omega