import Mathlib

theorem number_theory_317500
    (a b : ℕ) (ha : a.Prime) (hb : b.Prime) (h : a^2 + b = 2003) :
    a + b = 2001 := by
  by_cases h1 : a % 2 = 1
  · -- Assume a is odd, so a % 2 = 1
    have h2 : b % 2 = 0 := by
      have h3 : a % 2 = 1 := h1
      have h4 : a ^ 2 % 2 = 1 := by
        simp [Nat.pow_mod, h3]
      omega
    have h3 : b = 2 := by
      by_cases h4 : b > 2
      · -- Assume b > 2, so b is not 2
        have h5 : b % 2 = 0 := h2
        have h6 : ¬b.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ b by omega)
          all_goals omega
        tauto
      · -- Assume b ≤ 2, so b is 2
        interval_cases b <;> try tauto
    rw [h3] at h 
    have h4 : a ≤ 44 := by nlinarith
    have h7 : a ^ 2 = 2001 := by
      nlinarith 
    interval_cases a <;> norm_num at h7 <;> try { tauto }
  · -- Assume a is even, so a % 2 = 0
    have h2 : a % 2 = 0 := by
      omega
    have h3 : a = 2 := by
      by_cases h4 : a > 2
      · -- Assume a > 2, so a is not 2
        have h5 : a % 2 = 0 := h2
        have h6 : ¬a.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ a by omega)
          all_goals omega
        tauto
      · -- Assume a ≤ 2, so a is 2
        have h7 : a = 0 ∨ a = 1 ∨ a = 2 := by
          omega
        rcases h7 with (r | r | r)
        · 
          rw [r] at ha
          norm_num at ha
        · 
          rw [r] at ha
          norm_num at ha
        · 
          exact r
    rw [h3] at h 
    have h4 : b = 1999 := by
      nlinarith 
    omega