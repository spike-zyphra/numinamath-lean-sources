import Mathlib

theorem number_theory_64720 (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a * b * c = 24) (h' : Even (a + b + c)) (h'' : a + b + c < 25)
    (h''' : (a + b + c).divisors.card < 6) :
    a + b + c = 10 := by

  have h1 : a ≤ 24 := by
    have h24 : a ∣ 24 := by
      use b * c
      all_goals
        ring_nf
        all_goals
          nlinarith
    have h24' : a ∣ 24 := h24
    have h24_b : a ≤ 24 := by
      exact Nat.le_of_dvd (by norm_num) h24'
    exact h24_b

  have h2 : b ≤ 24 := by
    have h24 : b ∣ 24 := by
      use a * c
      all_goals
        ring_nf
        all_goals
          nlinarith
    have h24' : b ∣ 24 := h24
    have h24_b : b ≤ 24 := by
      exact Nat.le_of_dvd (by norm_num) h24'
    exact h24_b

  have h3 : c ≤ 24 := by
    have h24 : c ∣ 24 := by
      use a * b
      all_goals
        ring_nf
        all_goals
          nlinarith
    have h24' : c ∣ 24 := h24
    have h24_b : c ≤ 24 := by
      exact Nat.le_of_dvd (by norm_num) h24'
    exact h24_b

  interval_cases a <;> interval_cases b <;> try { 
    omega 
  } 
  <;> try { 
    interval_cases c <;> norm_num [Nat.even_iff] at h' 
    <;> try { 
      tauto 
    }
  }