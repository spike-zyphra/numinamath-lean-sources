import Mathlib

theorem number_theory_95708 {N: ℤ} (a b c: ℤ) (lb: 0 ≤ b) (rb: b ≤ 6)  
  (h1: N = 49 * a + 7 * b + c) (h2: N = 81 * c + 9 * b + a): b = 0 := by
  have h3 : 49 * a + 7 * b + c = 81 * c + 9 * b + a := by linarith
  omega