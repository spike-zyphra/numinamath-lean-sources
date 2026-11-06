import Mathlib

theorem number_theory_122478 (a b : ℕ) (ha : a < 10) (hb : b < 10)
    (h : (200 + 10 * a + 3) + 326 = 500 + 10 * b + 9) (h1 : 9 ∣ 500 + 10 * b + 9) :
    a + b = 6 := by
  have h2 : b = a + 2 := by
    omega
  rw [h2] at h1
  interval_cases a <;> omega
  <;> omega