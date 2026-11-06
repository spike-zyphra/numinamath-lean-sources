import Mathlib

theorem inequalities_70987 (a b c : ℝ) (ha : 0 ≤ c) (hc : c ≤ b) (hb : b ≤ a)
    (h1 : 5 ≥ a) (h2 : a + b ≤ 8) (h3 : a + b + c = 10) :
    a^2 + b^2 + c^2 ≤ 38 := by 
  have h4 : c = 10 - (a + b) := by linarith
  rw [h4]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - 5), sq_nonneg (b - (10 - (a + b))), sq_nonneg (a + b - 8), sq_nonneg (a - 4), sq_nonneg (b - 3), sq_nonneg ((10 - (a + b)) - 2)]