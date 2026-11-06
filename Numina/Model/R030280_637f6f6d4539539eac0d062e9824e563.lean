import Mathlib

theorem number_theory_95343 (p n d q : ℕ)
    (h : p * (1.55 : ℚ) + n * (1.95 : ℚ) + d * (1.35 : ℚ) + q * (1.75 : ℚ) = 14) :
    p + n + d + q = 8 := by 
  have eq1 : (p : ℚ) * 155 + (n : ℚ) * 195 + (d : ℚ) * 135 + (q : ℚ) * 175 = 1400 := by
    have h1 : p * (1.55 : ℚ) + n * (1.95 : ℚ) + d * (1.35 : ℚ) + q * (1.75 : ℚ) = 14 := h
    have eq2 : (p : ℚ) * (1.55 : ℚ) + (n : ℚ) * (1.95 : ℚ) + (d : ℚ) * (1.35 : ℚ) + (q : ℚ) * (1.75 : ℚ) = 14 := h1
    have eq3 : (p * (1.55 : ℚ) + n * (1.95 : ℚ) + d * (1.35 : ℚ) + q * (1.75 : ℚ) ) * (100 : ℚ) = (14 : ℚ) * (100 : ℚ) := by
      rw [eq2]
    ring_nf at eq3
    linarith
  have eq2 : p * 155 + n * 195 + d * 135 + q * 175 = 1400 := by
    exact_mod_cast eq1
  have h2 : p + n + d + q = 8 := by 
    have hp1 : p ≤ 9 := by 
      omega 
    have hn1 : n ≤ 7 := by 
      omega 
    have hd1 : d ≤ 10 := by 
      omega 
    have hq1 : q ≤ 8 := by 
      omega 
    interval_cases p <;> interval_cases n <;> omega
  exact h2