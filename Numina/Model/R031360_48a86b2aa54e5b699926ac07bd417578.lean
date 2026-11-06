import Mathlib

theorem number_theory_178503 (a b c : ℕ) (ha : a ≠ 0) (h : a ≤ 9) (h1 : b ≤ 9) (h2 : c ≤ 9)
    (h3 : (100 * a + 10 * c + b) + (100 * b + 10 * a + c) + (100 * b + 10 * c + a) +
      (100 * c + 10 * a + b) + (10 * b + a) = 3194) :
    100 * a + 10 * b + c = 358 := by 
  have h4 : a ≤ 9 := by linarith 
  have h5 : b ≤ 9 := by linarith 
  have h6 : c ≤ 9 := by linarith 
  interval_cases a <;> interval_cases b <;> omega