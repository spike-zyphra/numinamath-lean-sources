import Mathlib

theorem number_theory_132012 {a b c d : ℕ} (ha : a ≠ 0) (hsum : (1000 * a + 100 * b + 10 * c + d) + (1000 * c + 100 * d + 10 * a + b) = 3333) (hdiff : (1000 * a + 100 * b + 10 * c + d) - (1000 * c + 100 * d + 10 * a + b) = 693) :
    1000 * a + 100 * b + 10 * c + d = 2013 := by

  have eq1 : 1010 * a + 101 * b + 1010 * c + 101 * d = 3333 := by 
    omega
  have eq2 : 990 * a + 99 * b - 990 * c - 99 * d = 693 := by 
    omega
  have eq3 : 10 * (a + c) + (b + d) = 33 := by
    omega
  have eq4 : 10 * a + b - (10 * c + d) = 7 := by
    omega
  have h1 : a ≤ 3 := by
    omega
  have h2 : b ≤ 20 := by
    omega
  have h3 : c ≤ 3 := by
    omega
  have h4 : d ≤ 20 := by 
    omega
  interval_cases a <;> 
    try { 
      omega 
    } <;> 
        interval_cases c <;> 
          omega