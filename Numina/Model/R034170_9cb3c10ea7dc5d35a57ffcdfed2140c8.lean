import Mathlib

theorem number_theory_50364 (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (h1 : 2 * a - b + 7 * c = 1826) (h2 : 3 * a + 5 * b + 7 * c = 2007) :
    a = 7 := by
  have eq3 : a + 6 * b = 181 := by 
    omega
  have h3 : b ≤ 30 := by
    omega
  interval_cases b <;> norm_num at eq3 hb
  <;> try { 
    have h4 : a ≤ 181 := by 
      omega
    interval_cases a <;> norm_num at eq3 ha 
    <;> omega 
  }
  <;> norm_num at h1 h2 ⊢
  <;> try { 
    all_goals
    omega
  }