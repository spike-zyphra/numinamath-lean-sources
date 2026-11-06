import Mathlib

theorem number_theory_246582 (p q r : ℕ) (hpqr : p.Prime ∧ q.Prime ∧ r.Prime)
    (hqr : p > 3) (hpr : q > 3) (hqr' : r > 3) (hsum : (p + q + r).Prime) :
    6 ∣ p + q ∨ 6 ∣ p + r ∨ 6 ∣ q + r := by
  rcases hpqr with ⟨hp, hq, hr⟩
  have h1 : p % 2 = 1 := by
    by_contra h
    push_neg at h
    have h2 : ¬ p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
    tauto
  have h2 : q % 2 = 1 := by
    by_contra h
    push_neg at h
    have h2 : ¬ q.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega) (by omega) (by omega)
    tauto
  have h3 : r % 2 = 1 := by
    by_contra h
    push_neg at h
    have h2 : ¬ r.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ r by omega) (by omega) (by omega)
    tauto
  have h4 : p % 3 = 1 ∨ p % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h5 : p % 3 = 0 := by omega
    have h6 : 3 ∣ p := by
      omega
    have h5 : ¬ p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt h6 (by omega) (by omega)
    tauto
  have h5 : q % 3 = 1 ∨ q % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h5 : q % 3 = 0 := by omega
    have h6 : 3 ∣ q := by
      omega
    have h5 : ¬ q.Prime := by
      apply Nat.not_prime_of_dvd_of_lt h6 (by omega) (by omega)
    tauto
  have h6 : r % 3 = 1 ∨ r % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h5 : r % 3 = 0 := by omega
    have h6 : 3 ∣ r := by
      omega
    have h5 : ¬ r.Prime := by
      apply Nat.not_prime_of_dvd_of_lt h6 (by omega) (by omega)
    tauto
  have h7 : p % 6 = 1 ∨ p % 6 = 5 := by 
    omega
  have h8 : q % 6 = 1 ∨ q % 6 = 5 := by 
    omega
  have h9 : r % 6 = 1 ∨ r % 6 = 5 := by 
    omega
  by_contra h
  push_neg at h
  -- Assume none of the sums is divisible by 6
  -- We need to derive a contradiction
  -- First, show the total sum is divisible by 3
  have h12 : (p + q + r) % 3 = 0 := by 
    omega
  -- Now, show that this contradicts that p + q + r is prime
  have h13 : ¬ (p + q + r).Prime := by
    apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + q + r) by omega)
    all_goals
      linarith
  tauto