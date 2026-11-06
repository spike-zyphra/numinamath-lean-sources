import Mathlib

theorem number_theory_260160 (p q r s : ℕ) (hpqr : p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime)
    (hqr : p < q ∧ q < r) (hps : r < s) (hsum : p + 10 > s) (h : 5 < p) :
    60 ∣ p + q + r + s := by
  rcases hpqr with ⟨hp, hq, hr, hs⟩
  have h1 : p % 2 = 1 := by 
    by_contra h2
    push_neg at h2
    have h2' : p % 2 = 0 := by omega
    have h3 : ¬p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals omega
    tauto
  have h2 : q % 2 = 1 := by 
    by_contra h2
    push_neg at h2
    have h2' : q % 2 = 0 := by omega
    have h3 : ¬q.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
      all_goals omega
    tauto
  have h3 : r % 2 = 1 := by 
    by_contra h2
    push_neg at h2
    have h2' : r % 2 = 0 := by omega
    have h3 : ¬r.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ r by omega)
      all_goals omega
    tauto
  have h4 : s % 2 = 1 := by 
    by_contra h2
    push_neg at h2
    have h2' : s % 2 = 0 := by omega
    have h3 : ¬s.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ s by omega)
      all_goals omega
    tauto
  have h5 : p % 3 = 1 ∨ p % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h5 : p % 3 = 0 := by omega
    have h6 : p > 3 := by linarith
    have h7 : ¬p.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
      all_goals omega
    tauto
  have h6 : q % 3 = 1 ∨ q % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h5 : q % 3 = 0 := by omega
    have h7 : q > 3 := by linarith
    have h8 : ¬q.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega)
      all_goals omega
    tauto
  have h7 : r % 3 = 1 ∨ r % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h5 : r % 3 = 0 := by omega
    have h7 : r > 3 := by linarith
    have h8 : ¬r.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ r by omega)
      all_goals omega
    tauto
  have h8 : s % 3 = 1 ∨ s % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h5 : s % 3 = 0 := by omega
    have h7 : s > 3 := by linarith
    have h8 : ¬s.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ s by omega)
      all_goals omega
    tauto
  have h9 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by 
    by_contra h
    push_neg at h
    have h5 : p % 5 = 0 := by omega
    have h6 : p > 5 := by linarith
    have h7 : ¬p.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega)
      all_goals omega
    tauto
  have h10 : q % 5 = 1 ∨ q % 5 = 2 ∨ q % 5 = 3 ∨ q % 5 = 4 := by 
    by_contra h
    push_neg at h
    have h5 : q % 5 = 0 := by omega
    have h7 : q > 5 := by linarith
    have h8 : ¬q.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ q by omega)
      all_goals omega
    tauto
  have h11 : r % 5 = 1 ∨ r % 5 = 2 ∨ r % 5 = 3 ∨ r % 5 = 4 := by 
    by_contra h
    push_neg at h
    have h5 : r % 5 = 0 := by omega
    have h7 : r > 5 := by linarith
    have h8 : ¬r.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ r by omega)
      all_goals omega
    tauto
  have h12 : s % 5 = 1 ∨ s % 5 = 2 ∨ s % 5 = 3 ∨ s % 5 = 4 := by 
    by_contra h
    push_neg at h
    have h5 : s % 5 = 0 := by omega
    have h7 : s > 5 := by linarith
    have h8 : ¬s.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ s by omega)
      all_goals omega
    tauto
  omega