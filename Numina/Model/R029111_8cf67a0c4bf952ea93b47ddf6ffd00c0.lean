import Mathlib

theorem number_theory_88790 {a b c : ℤ} (ha : a ≥ 4) (hb : b ≥ 4) (hc : c ≥ 4)
    (hne : ¬(a = b ∧ b = c)) (h : 4*a*b*c = (a + 3)*(b + 3)*(c + 3)) :
    a + b + c = 16 := by 
  have h1 : a ≤ 22 := by
    nlinarith [sq_nonneg (a - 22), sq_nonneg (b - 4), sq_nonneg (c - 4),
      mul_nonneg (show (0 : ℤ) ≤ a - 4 by nlinarith) (show (0 : ℤ) ≤ b - 4 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ a - 4 by nlinarith) (show (0 : ℤ) ≤ c - 4 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ b - 4 by nlinarith) (show (0 : ℤ) ≤ c - 4 by nlinarith)]
  have h2 : b ≤ 22 := by
    nlinarith [sq_nonneg (b - 22), sq_nonneg (a - 4), sq_nonneg (c - 4),
      mul_nonneg (show (0 : ℤ) ≤ a - 4 by nlinarith) (show (0 : ℤ) ≤ b - 4 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ a - 4 by nlinarith) (show (0 : ℤ) ≤ c - 4 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ b - 4 by nlinarith) (show (0 : ℤ) ≤ c - 4 by nlinarith)]
  have h3 : c ≤ 22 := by
    nlinarith [sq_nonneg (c - 22), sq_nonneg (a - 4), sq_nonneg (b - 4),
      mul_nonneg (show (0 : ℤ) ≤ a - 4 by nlinarith) (show (0 : ℤ) ≤ b - 4 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ a - 4 by nlinarith) (show (0 : ℤ) ≤ c - 4 by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ b - 4 by nlinarith) (show (0 : ℤ) ≤ c - 4 by nlinarith)]
  interval_cases a <;> interval_cases b <;> omega