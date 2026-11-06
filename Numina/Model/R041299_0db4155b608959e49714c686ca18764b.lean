import Mathlib

theorem number_theory_1534 {p q : ℕ} [hp : Fact (p.Prime)] (hq : q.Prime)
    (h : p * 1 + 5 * q = 97) : (p : ℤ) ^ 2 - q = -15 := by
  have eq1 : p + 5 * q = 97 := by 
    omega
  have h2 : p ≤ 97 := by 
    omega 
  have h3 : q ≤ 19 := by 
    omega 
  have hp' : p.Prime := by
    simpa using hp.1 
  interval_cases q <;> norm_num at h3 hq eq1
  <;> try { 
    interval_cases p <;> norm_num at hp' eq1 
    <;> omega 
  }