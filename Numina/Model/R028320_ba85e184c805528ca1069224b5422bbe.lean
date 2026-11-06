import Mathlib

theorem number_theory_166820 (a b c d : ℕ) (ha : a ≠ 0) (h : 3 ∣ (1000 * a + 100 * b + 10 * c + d))
    (h1 : a + b + d = 11) (h2 : a + c + d = 12) (h3 : b + c + d = 10) :
    1000 * a + 100 * b + 10 * c + d = 5343 ∨ 1000 * a + 100 * b + 10 * c + d = 2019 := by
  have h4 : c = b + 1 := by
    omega
  have h5 : a = b + 2 := by
    omega
  have h6 : 2 * b + d = 9 := by
    omega
  have h7 : b ≤ 4 := by 
    omega
  have h8 : b < 5 := by 
    omega
  interval_cases b <;> norm_num [h4, h5, h6] at *
  <;> omega