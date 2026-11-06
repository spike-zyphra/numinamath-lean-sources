import Mathlib

theorem number_theory_8165
(a b : ℕ)
(ha : a.Prime)
(hb : b.Prime)
(hdiff : a - b = 39) :
(-1 : ℤ) * a ^ b = -1681 := by 
  have h1 : a = b + 39 := by 
    omega
  rw [h1] at ha 
  by_contra h
  push_neg at h
  have h3 : b ≤ 42 := by 
    by_contra h4
    push_neg at h4
    have h41 : b % 2 = 1 := by
      by_contra h411
      push_neg at h411
      have h4111 : b % 2 = 0 := by omega
      have h5111 : ¬b.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ b by omega)
        all_goals
          nlinarith
        all_goals
          nlinarith
      contradiction
    have h42 : (b + 39) % 2 = 0 := by
      omega
    have h6 : ¬(b + 39).Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (b + 39) by omega)
      all_goals
        nlinarith
      all_goals
        nlinarith
    contradiction
  interval_cases b <;> norm_num at ha hb h1 ⊢ <;> try { 
    simp [h1, pow_succ, mul_add, add_mul] at h ⊢ 
    all_goals 
      omega 
  }
  <;> norm_num at ha hb h1 ⊢ <;> omega