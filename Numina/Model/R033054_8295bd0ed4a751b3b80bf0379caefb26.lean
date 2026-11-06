import Mathlib

theorem algebra_7356 {m n p q : ℝ} (h1 : m + n + p + q = 22) (h2 : m * p = 100) (h3 : n * q = 100) :
    Real.sqrt ((m + n) * (n + p) * (p + q) * (q + m)) = 220 := by
  have h6 : (m + n) * (n + p) * (p + q) * (q + m) = 48400 := by
    nlinarith [sq_nonneg (m + p - (n + q)), sq_nonneg (m - p), sq_nonneg (n - q), sq_nonneg (m + p + n + q), sq_nonneg (m * q - n * p), sq_nonneg (n * m - p * q)]
  have h7 : Real.sqrt ((m + n) * (n + p) * (p + q) * (q + m)) = 220 := by
    rw [h6]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  exact h7