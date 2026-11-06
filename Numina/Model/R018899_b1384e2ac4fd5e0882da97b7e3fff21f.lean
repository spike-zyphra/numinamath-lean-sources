import Mathlib

theorem number_theory_275581 (n : ℕ) :
    (8 ∣ n) ↔ (8 ∣ (n % 10) + 2 * ((n / 10) % 10) + 4 * ((n / 100) % 10)) := by
  constructor
  · -- Forward direction: if $8 ∣ n$, then $8 ∣ \text{sum}$
    intro h
    have h1 : n % 8 = 0 := by 
      omega
    have h2 : (n % 10 + 2 * (n / 10 % 10) + 4 * (n / 100 % 10)) % 8 = 0 := by
      have h4 : (n % 10 + 2 * (n / 10 % 10) + 4 * (n / 100 % 10)) % 8 = n % 8 := by
        have h6 : n % 10 < 10 := by
          omega
        have h7 : (n / 10) % 10 < 10 := by
          omega
        have h8 : (n / 100) % 10 < 10 := by
          omega
        have h14 : (n % 10 + 2 * (n / 10 % 10) + 4 * (n / 100 % 10)) % 8 = n % 8 := by
          have h9 : (n % 10 + 2 * (n / 10 % 10) + 4 * (n / 100 % 10)) % 8 = ((n % 10) + (2 * ((n / 10) % 10)) + (4 * ((n / 100) % 10)) ) % 8 := by 
            omega
          have h10 : n % 8 = ( (4 * ((n / 100) % 10)) + (2 * ((n / 10) % 10)) + (n % 10) ) % 8 := by
            have h12 : n % 8 = n % 8 := by 
              omega
            have : (n) = 100 * (n / 100) + (n % 100) := by
              omega
            have : (n % 100) = 10 * (n / 10 % 10) + (n % 10) := by
              omega
            omega
          omega
        assumption
      omega
    have h3 : 8 ∣ (n % 10 + 2 * (n / 10 % 10) + 4 * (n / 100 % 10)) := by 
      omega
    exact h3
  · -- Backward direction: if 8 divides the sum, then 8 divides n
    intro h
    have h1 : ((n % 10) + 2 * ((n / 10) % 10) + 4 * ((n / 100) % 10)) % 8 = 0 := by
      omega
    have h2 : n % 8 = 0 := by
      have h4 : (n % 10 + 2 * (n / 10 % 10) + 4 * (n / 100 % 10)) % 8 = n % 8 := by
        have h6 : n % 10 < 10 := by
          omega
        have h7 : (n / 10) % 10 < 10 := by
          omega
        have h8 : (n / 100) % 10 < 10 := by
          omega
        have h14 : (n % 10 + 2 * (n / 10 % 10) + 4 * (n / 100 % 10)) % 8 = n % 8 := by
          have h9 : (n % 10 + 2 * (n / 10 % 10) + 4 * (n / 100 % 10)) % 8 = ((n % 10) + (2 * ((n / 10) % 10)) + (4 * ((n / 100) % 10)) ) % 8 := by 
            omega
          have h10 : n % 8 = ( (4 * ((n / 100) % 10)) + (2 * ((n / 10) % 10)) + (n % 10) ) % 8 := by
            have h12 : n % 8 = n % 8 := by 
              omega
            have : (n) = 100 * (n / 100) + (n % 100) := by
              omega
            have : (n % 100) = 10 * (n / 10 % 10) + (n % 10) := by
              omega
            omega
          omega
        assumption
      omega
    have h3 : 8 ∣ n := by 
      omega
    exact h3