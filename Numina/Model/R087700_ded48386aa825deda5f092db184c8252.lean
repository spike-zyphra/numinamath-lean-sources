import Mathlib

theorem algebra_244232 (a m : ℕ) (ha : 0 < a) (hm : 0 < m)
    (h : a < m) (h' : a * m + a + m = 59) :
    a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by
  have h1 : a ≤ 59 := by 
    nlinarith [h']
  have h2 : m ≤ 59 := by 
    nlinarith [h']
  interval_cases a <;> omega