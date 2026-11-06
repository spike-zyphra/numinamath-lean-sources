import Mathlib

theorem number_theory_275177 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c = 42) (h' : a + b = 9) : c = 3 := by
  have h1 : a ≤ 9 := by 
    linarith 
  have h2 : b = 9 - a := by 
    omega 
  rw [h2] at h 
  interval_cases a <;> omega 
  <;> try { all_goals linarith }