import Mathlib

theorem algebra_199289 {a r : ℤ} (hr : r ≠ 0) (h1 : a * r = a + 2) (h2 : a * r * (a + 2) = a * r + 16) :
    a = 1 ∧ r = 3 := by 
  have eq1 : a * r = a + 2 := h1
  have eq2 : a * r * (a + 2) = a * r + 16 := h2 
  have eq3 : (a + 2) * (a + 2) = (a + 2) + 16 := by
    rw [show a * r = a + 2 by linarith] at eq2
    nlinarith
  exfalso 
  have h3 : (a + 2) * (a + 2) - (a + 2) - 16 = 0 := by
    linarith [eq3]
  have h4 : (a + 2) ≤ 8 := by
    nlinarith [sq_nonneg ((a + 2 - 1 : ℤ)), sq_nonneg ((a + 2 : ℤ)), sq_nonneg ((a + 2) ^ 2 - (a + 2) - 16) ]
  have h5 : (a + 2) ≥ -8 := by
    nlinarith [sq_nonneg ((a + 2 - 1 : ℤ)), sq_nonneg ((a + 2 : ℤ)), sq_nonneg ((a + 2) ^ 2 - (a + 2) - 16) ]
  interval_cases (a + 2) <;> try { 
    omega
  }