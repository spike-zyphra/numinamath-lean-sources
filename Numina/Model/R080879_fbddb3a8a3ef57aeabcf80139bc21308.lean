import Mathlib

open Real

theorem calculus_83714 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 5) :
    5 * a + 3 * b + (11 * c - c ^ 2) ≤ 34 := by 
  nlinarith [sq_nonneg (a - 2), sq_nonneg (b), sq_nonneg (c - 3),
    mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith),
    mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ c by linarith),
    mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ c by linarith)]