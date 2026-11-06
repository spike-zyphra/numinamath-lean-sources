import Mathlib

/- The first term of a geometric sequence is 729, and the 7th term is 64. What is the positive, real value for the 5th term? -/
theorem algebra_10608 {a r : ℝ} (h1 : a = 729) (h2 : a * r^6 = 64) :
    a * r^4 = 144 := by 
  rw [h1] at h2 ⊢
  nlinarith [h2, sq_nonneg (r ^ 2)]