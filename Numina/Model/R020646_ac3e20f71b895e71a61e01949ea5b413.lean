import Mathlib

theorem number_theory_185561 (p q r : ℕ) (hpqr : p.Prime ∧ q.Prime ∧ r.Prime)
    (hqr : p > 3) (hpr : q > 3) (hqr' : r > 3) (h : 3 ∣ p + q + r) :
    6 ∣ p - q ∧ 6 ∣ p - r ∧ 6 ∣ q - r := by
  rcases hpqr with ⟨hp, hq, hr⟩
  have h1 : p % 3 = 1 ∨ p % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h2 : p % 3 = 0 := by
      omega
    have h3 : p > 3 := hqr
    have h4 : ¬ p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
      all_goals omega
    contradiction
  have h2 : q % 3 = 1 ∨ q % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h3 : q % 3 = 0 := by
      omega
    have h4 : q > 3 := hpr
    have h5 : ¬ q.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega)
      all_goals omega
    contradiction
  have h3 : r % 3 = 1 ∨ r % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h4 : r % 3 = 0 := by
      omega
    have h5 : r > 3 := hqr'
    have h6 : ¬ r.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ r by omega)
      all_goals omega
    contradiction
  have h4 : p % 3 = q % 3 := by 
    omega
  have h5 : p % 3 = r % 3 := by 
    omega
  have h6 : q % 3 = r % 3 := by
    omega
  have h81 : p % 2 = 1 := by 
    by_contra h
    push_neg at h
    have h2 : p % 2 = 0 := by 
      omega
    have h4 : p > 2 := by
      omega
    have h5 : ¬p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals omega
    contradiction
  have h82 : q % 2 = 1 := by 
    by_contra h
    push_neg at h
    have h3 : q % 2 = 0 := by 
      omega
    have h4 : q > 2 := by
      omega
    have h5 : ¬q.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
      all_goals omega
    contradiction
  have h83 : r % 2 = 1 := by 
    by_contra h
    push_neg at h
    have h4 : r % 2 = 0 := by 
      omega
    have h5 : r > 2 := by
      omega
    have h6 : ¬r.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ r by omega)
      all_goals omega
    contradiction
  constructor
  · -- Show that 6 divides p - q
    omega
  constructor
  · -- Show that 6 divides p - r
    omega
  · -- Show that 6 divides q - r
    omega