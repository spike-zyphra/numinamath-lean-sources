import Mathlib

theorem algebra_234772 {a d : ℤ} (h : a > 0) (h' : d > 0)
    (h'' : a * (1 + 4 * d) = 80 - a - d - a - 4 * d) :
    a = 2 ∧ d = 4 := by
  have eq1 : 4 * a * d + 3 * a + 5 * d = 80 := by
    nlinarith
  
  have h1 : d ≤ 15 := by 
    nlinarith [show 0 < a from h, show 0 < d from h']

  interval_cases d <;> try { 
    omega
  }