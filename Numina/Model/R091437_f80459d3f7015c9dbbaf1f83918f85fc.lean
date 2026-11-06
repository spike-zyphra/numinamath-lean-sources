import Mathlib

theorem algebra_209140 {x : ℝ} (hx : x^11 + x^7 + x^3 = 1) :
    (x^4 + x^3 - 1) = x^(15 : ℕ) := by
  have eq1 : x^11 = 1 - x ^ 7 - x ^ 3 := by
    linarith
  have eq2 : x ^ 12 = x * x ^ 11 := by
    ring_nf
  rw [eq1] at eq2
  have eq3 : x ^ 12 = x - x^8 - x^4 := by 
    nlinarith
  have eq4 : x ^ 13 = x * x ^ 12 := by 
    ring_nf
  rw [eq3] at eq4
  have eq5 : x ^ 13 = x^2 - x^9 - x^5 := by 
    nlinarith
  have eq6 : x ^ 14 = x * x ^ 13 := by 
    ring_nf
  rw [eq5] at eq6
  have eq7 : x ^ 14 = x^3 - x^10 - x^6 := by 
    nlinarith
  have eq8 : x ^ 15 = x * x ^ 14 := by 
    ring_nf
  rw [eq7] at eq8
  have eq9 : x ^ 15 = x^4 - x ^ 11 - x^7 := by 
    nlinarith
  rw [eq1] at eq9
  have eq10 : x ^ 15 = x^4 + x^3 - 1 := by 
    nlinarith
  linarith [eq10]