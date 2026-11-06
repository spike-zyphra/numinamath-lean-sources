import Mathlib

theorem inequalities_25842 (a b c : ℝ) (h₀ : a + b + c = 0) :
    a * b^3 + b * c^3 + c * a^3 ≤ 0 := by
  have h1 : c = -(a + b) := by linarith 
  rw [h1]
  nlinarith [sq_nonneg (a^2 + a * b + b^2), sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a * b), sq_nonneg ((a + b)^2), sq_nonneg ((a + b)*b), sq_nonneg ((a + b)*a), sq_nonneg (a^3 + b^3), sq_nonneg (a * (a + b)), sq_nonneg (b * (a + b)), sq_nonneg ((a + b) * (a * b)), sq_nonneg ((a + b)^2), sq_nonneg ((a + b)^3)]