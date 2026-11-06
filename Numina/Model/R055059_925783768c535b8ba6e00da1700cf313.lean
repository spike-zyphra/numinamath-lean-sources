import Mathlib

theorem number_theory_216532 (p q r s : ℕ) (hpqr : p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime)
    (hqr : q < r) (hps : p < s) (hsum : p + 10 > s) (h5 : 5 < p) (h1 : p < q) (h2 : q < r)
    (h3 : r < s) :
    60 ∣ p + q + r + s := by
  rcases hpqr with ⟨hp, hq, hr, hs⟩
  have hp1 : p % 2 = 1 := by
    by_contra h
    push_neg at h
    have h2dvd : 2 ∣ p := by omega
    have : ¬ p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt h2dvd (by omega) (by omega)
    contradiction
  have hq1 : q % 2 = 1 := by
    by_contra h
    push_neg at h
    have h2dvd : 2 ∣ q := by omega
    have : ¬ q.Prime := by
      apply Nat.not_prime_of_dvd_of_lt h2dvd (by omega) (by omega)
    contradiction
  have hr1 : r % 2 = 1 := by
    by_contra h
    push_neg at h
    have h2dvd : 2 ∣ r := by omega
    have : ¬ r.Prime := by
      apply Nat.not_prime_of_dvd_of_lt h2dvd (by omega) (by omega)
    contradiction
  have hs1 : s % 2 = 1 := by
    by_contra h
    push_neg at h
    have h2dvd : 2 ∣ s := by omega
    have : ¬ s.Prime := by
      apply Nat.not_prime_of_dvd_of_lt h2dvd (by omega) (by omega)
    contradiction
  have hp3 : p % 3 = 1 ∨ p % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h3dvd : 3 ∣ p := by omega
    have : ¬ p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt h3dvd (by omega) (by omega)
    contradiction
  have hq3 : q % 3 = 1 ∨ q % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h3dvd : 3 ∣ q := by omega
    have : ¬ q.Prime := by
      apply Nat.not_prime_of_dvd_of_lt h3dvd (by omega) (by omega)
    contradiction
  have hr3 : r % 3 = 1 ∨ r % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h3dvd : 3 ∣ r := by omega
    have : ¬ r.Prime := by
      apply Nat.not_prime_of_dvd_of_lt h3dvd (by omega) (by omega)
    contradiction
  have hs3 : s % 3 = 1 ∨ s % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h3dvd : 3 ∣ s := by omega
    have : ¬ s.Prime := by
      apply Nat.not_prime_of_dvd_of_lt h3dvd (by omega) (by omega)
    contradiction
  have hp5 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by 
    by_contra h
    push_neg at h
    have h5dvd : 5 ∣ p := by omega
    have : ¬ p.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt h5dvd (by omega) (by omega)
    contradiction
  have hq5 : q % 5 = 1 ∨ q % 5 = 2 ∨ q % 5 = 3 ∨ q % 5 = 4 := by 
    by_contra h
    push_neg at h
    have h5dvd : 5 ∣ q := by omega
    have : ¬ q.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt h5dvd (by omega) (by omega)
    contradiction
  have hr5 : r % 5 = 1 ∨ r % 5 = 2 ∨ r % 5 = 3 ∨ r % 5 = 4 := by 
    by_contra h
    push_neg at h
    have h5dvd : 5 ∣ r := by omega
    have : ¬ r.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt h5dvd (by omega) (by omega)
    contradiction
  have hs5 : s % 5 = 1 ∨ s % 5 = 2 ∨ s % 5 = 3 ∨ s % 5 = 4 := by 
    by_contra h
    push_neg at h
    have h5dvd : 5 ∣ s := by omega
    have : ¬ s.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt h5dvd (by omega) (by omega)
    contradiction
  omega