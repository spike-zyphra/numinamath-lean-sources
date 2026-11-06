import Mathlib

theorem algebra_126961 {a b c m n : ℤ} (ha : a ≠ 0) (h : a * m ^ 2 + b * m + c - (a * n ^ 2 + b * n + c) = 1) :
    |m - n| = 1 := by 
  have h1 : (m - n) * (a * (m + n) + b) = 1 := by linarith 
  have h2 : m - n = 1 ∨ m - n = -1 := by 
    have : m - n = 1 ∨ m - n = -1 := by 
      apply Int.eq_one_or_neg_one_of_mul_eq_one 
      exact h1
    exact this
  cases' h2 with h3 h4
  · rw [h3]
    norm_num
  · rw [h4]
    norm_num