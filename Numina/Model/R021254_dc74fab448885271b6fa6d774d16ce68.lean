import Mathlib

theorem algebra_324845 {m n p q : ℝ} (h₀ : m + n + p + q = 22) (h₁ : m * p = 100) (h₂ : n * q = 100) :
    Real.sqrt ((m + n) * (n + p) * (p + q) * (q + m)) = 220 := by
  have h3 : (m + n) * (n + p) * (p + q) * (q + m) = 48400 := by
    nlinarith [sq_nonneg (m - p), sq_nonneg (n - q), sq_nonneg (m + p - (n + q))]
  rw [h3]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num