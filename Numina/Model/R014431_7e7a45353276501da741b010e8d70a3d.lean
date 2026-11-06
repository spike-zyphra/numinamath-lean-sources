import Mathlib

theorem number_theory_124192
    (a b c : ℕ)
    (ha : a.Prime)
    (hb : b.Prime)
    (hc : c.Prime)
    (h1 : a + b = 49)
    (h2 : b + c = 60) :
    c = 13 := by
  have h3 : a ≤ 49 := by
    omega
  have h4 : b ≤ 49 := by 
    omega
  have h5 : c ≤ 60 := by 
    omega

  by_cases h : a % 2 = 1
  · -- Assume a is odd, then b must be even (since a + b = 49, odd + even = odd)
    have h10 : a % 2 = 1 := h
    have h11 : b % 2 = 0 := by 
      omega

    have h12 : b = 2 := by
      by_cases h12 : b > 2
      · -- Assume b > 2, we show contradiction
        -- Since b is even and greater than 2, it's not prime
        have h13 : ¬b.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ b by omega)
          all_goals linarith
        contradiction
      · -- Assume b ≤ 2
        interval_cases b <;> norm_num at *
    
    -- From a + b = 49 and b = 2, we get a = 47
    have h14 : a = 47 := by 
      omega

    -- From b + c = 60 and b = 2, we get c = 58
    have h15 : c = 58 := by 
      omega

    -- Show contradiction since 58 is not prime
    rw [h15] at hc
    norm_num at hc
  · -- Assume a is even, so a must be 2
    have h10 : a % 2 = 0 := by 
      omega
    
    have h13 : a = 2 := by
      by_cases h14 : a > 2
      · -- Assume a > 2
        -- Since a is even and greater than 2, it's not prime
        have h16 : ¬a.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ a by omega)
          all_goals linarith
        contradiction
      · -- Assume a <= 2
        interval_cases a <;> norm_num at *
    
    -- From a + b = 49 and a = 2, we get b = 47
    have h14 : b = 47 := by
      omega

    -- From b + c = 60 and b = 47, we get c = 13
    have h15 : c = 13 := by
      omega
    exact h15