import Mathlib

theorem number_theory_104798 (k : ℕ) (h : k > 0) (a b : ℕ)
    (ha : a > 0) (hb : b > 0) (h1 : a + b > 0) (h2 : a > 75 * (a + b) / 100)
    (h3 : a < 80 * (a + b) / 100) (h4 : a * 1 + b * (-k : ℤ) = k) :
    k = 3 := by 
  have eq : (a : ℤ) - (b : ℤ) * (k : ℤ) = (k : ℤ) := by 
    linarith
  have h5 : a < 4 * b := by 
    omega
  have h6 : a > 3 * b := by 
    omega
  have eq_a : (a : ℤ) = (b : ℤ) * (k : ℤ) + (k : ℤ) := by
    linarith [eq]
  have h7 : k ≤ 5 := by 
    by_cases h7 : k ≤ 5
    · exact h7
    · exfalso
      push_neg at h7
      have h6' : k ≥ 6 := by omega
      have h7 : (a : ℤ) ≥ 6 * ((b : ℤ) + 1) := by 
        nlinarith [eq_a, show (k : ℤ) ≥ 6 by exact_mod_cast h6']
      have h8 : (a : ℤ) < 4 * (b : ℤ) := by 
        have h6_nat : a < 4 * b := by 
          omega 
        have h6_int : (a : ℤ) < 4 * (b : ℤ) := by 
          exact_mod_cast h6_nat 
        linarith 
      nlinarith
  have h8 : k > 2 := by 
    by_cases h8 : k > 2
    · exact h8
    · exfalso
      push_neg at h8
      have h9 : k ≤ 2 := by 
        omega 
      interval_cases k <;> 
        try { 
          omega 
        } <;> 
          try { 
            exfalso 
            nlinarith [show (a : ℤ) = (b : ℤ) * (k : ℤ) + (k : ℤ) from eq_a]
          }
  interval_cases k <;> omega