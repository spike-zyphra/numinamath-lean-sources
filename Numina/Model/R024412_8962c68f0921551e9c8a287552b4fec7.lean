import Mathlib

theorem algebra_284695 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 11) :
    a * b ≤ 30 := by
  have h1 : b = 11 - a := by 
    omega
  rw [h1]
  have h2 : a ≤ 10 := by
    omega
  interval_cases a <;> omega