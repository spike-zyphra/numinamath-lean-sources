import Mathlib

theorem number_theory_130611 (a b : ℕ) (ha : a.Prime) (hb : b.Prime) (h : 5 * a + b = 2027) : a + b = 2019 := by
  have h1 : b = 2027 - 5 * a := by
    omega 
  have h3 : a ≤ 2027 := by
    linarith
  have h4 : b ≤ 2027 := by
    omega
  by_cases h9 : Even a
  · -- Assume a is even
    have h10 : a % 2 = 0 := by 
      have h9' : Even a := by 
        simpa using h9 
      obtain ⟨k, hk⟩ := h9' 
      omega 
    have ha1 : a = 2 := by
      by_cases h11 : a > 2
      · -- Assume a > 2
        have h12 : a % 2 = 0 := h10
        have h13 : ¬ Nat.Prime a := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ a by omega) (by linarith) (by linarith)
        contradiction
      · -- Assume a ≤ 2
        have : a ≤ 2 := by linarith
        interval_cases a <;> norm_num at *
        all_goals tauto
    have hb1 : b = 2017 := by 
      rw [ha1] at h 
      linarith 
    linarith 
  · -- Assume a is not even
    have h9 : ¬ Even a := by
      simpa using h9
    have h11 : a % 2 = 1 := by
      have h9' : Odd a := by
        simpa using h9
      obtain ⟨k, hk⟩ := h9' 
      omega
    have h11' : b % 2 = 0 := by
      omega
    have h10 : Even b := by
      simp [Nat.even_iff, h11']
    by_cases h11 : b = 2
    · -- Assume b = 2
      have h12 : 5 * a = 2025 := by 
        linarith 
      have h13 : a = 405 := by 
        omega 
      rw [h13] at ha 
      norm_num at ha 
      all_goals try tauto
    · -- Assume b ≠ 2
      have h9' : b > 2 := by 
        by_contra h
        push_neg at h
        have : b ≤ 2 := by linarith
        omega 
      have h10' : Nat.Prime b := hb 
      have h11' : b % 2 = 0 := h11'
      have h16 : ¬ Nat.Prime b := by 
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ b by omega) (by linarith) (by linarith) 
      contradiction