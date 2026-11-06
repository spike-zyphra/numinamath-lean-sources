import Mathlib

theorem algebra_226503 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 1 < a) (h2 : a < b) (h3 : b < c) (h4 : a + b + c = 111) (h5 : b^2 = a * c) :
    b = 36 := by 
  have h6 : a + c = 111 - b := by 
    omega
  have h7 : a < b := by linarith
  have h8 : b < c := by linarith
  have h9 : b < 57 := by
    nlinarith
  have h10 : a < 56 := by
    nlinarith
  have h11 : c < 111 := by
    nlinarith
  interval_cases b <;> try { 
    omega 
  }
  <;> try { 
    interval_cases a <;> omega 
  }