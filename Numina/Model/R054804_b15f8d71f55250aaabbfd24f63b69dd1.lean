import Mathlib

theorem algebra_292806 (a b : ℕ) (ha : a > 0) (hb : b > 0)
    (h : 2 * a + b = 60) :
    a * b ≤ 450 := by 
  have h1 : b = 60 - 2 * a := by 
    omega 
  rw [h1]
  have h2 : a ≤ 30 := by
    omega
  interval_cases a <;> omega