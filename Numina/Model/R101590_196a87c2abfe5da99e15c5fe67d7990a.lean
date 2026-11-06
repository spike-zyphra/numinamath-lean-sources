import Mathlib

theorem algebra_41723 {p q r : ℝ} (hqr : q ≠ 0) (hpr : p ≠ 0) (hqr' : r ≠ 0)
    (h1 : (p + q) * (q + r) * (r + p) / (p * q * r) = 24) (h2 : (p - 2 * q) * (q - 2 * r) * (r - 2 * p) / (p * q * r) = 10) :
    ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ Nat.Coprime m n ∧ (p / q + q / r + r / p) = m / n := by
  have eq1 : (p + q) * (q + r) * (r + p) = 24 * (p * q * r) := by
    have hne : p * q * r ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact hpr
      exact hqr
      exact hqr'
    field_simp at h1 ⊢
    linarith
  have eq2 : (p - 2 * q) * (q - 2 * r) * (r - 2 * p) = 10 * (p * q * r) := by
    have hne : p * q * r ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact hpr
      exact hqr
      exact hqr'
    field_simp at h2 ⊢
    linarith
  have h3 : p / q + q / r + r / p = 61 / 6 := by
    have eq3 : p ^ 2 * r + q ^ 2 * p + r ^ 2 * q = 61 / 6 * (p * q * r) := by
      have hne : p * q * r ≠ 0 := by
        apply mul_ne_zero
        apply mul_ne_zero
        exact hpr
        exact hqr
        exact hqr'
      nlinarith [sq_nonneg (p * q - q * r), sq_nonneg (q * r - r * p), sq_nonneg (r * p - p * q),
        sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (r - p),
        eq1, eq2, mul_ne_zero (mul_ne_zero hpr hqr) hqr']
    have hne : p * q * r ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact hpr
      exact hqr
      exact hqr'
    field_simp [hne]
    nlinarith [eq3]
  use 61, 6
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · linarith [h3]