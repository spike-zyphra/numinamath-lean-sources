import Mathlib

theorem number_theory_294404 {a b : ℕ} (ha : a % 3 = 2) (hb : b % 7 = 5)
    (h : a + b = 100) :
    a * b ≤ 2491 := by
  have h1 : b = 100 - a := by
    omega
  rw [h1] at hb
  have h2 : a ≤ 100 := by omega
  interval_cases a <;> norm_num at ha hb <;> omega