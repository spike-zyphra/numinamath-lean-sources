import Mathlib

theorem algebra_825 (x y a b : ℝ) (h : abs (2 * x - y) + (a - 3 * b) ^ 2 = 0) (m : 3 * a ^ 3 * x ^ 2 + a * b ^ 2 * y ^ 2 + 2 * b ^ 3 * x * y ≠ 0):
    (2 * a ^ 3 * x ^ 2 + a * b ^ 2 * y ^ 2 + 3 * b ^ 3 * x * y) / (3 * a ^ 3 * x ^ 2 + a * b ^ 2 * y ^ 2 + 2 * b ^ 3 * x * y) = 72 / 97 := by
  have h1 : abs (2 * x - y) = 0 := by
    linarith [abs_nonneg (2 * x - y), sq_nonneg (a - 3 * b)]
  have h2 : 2 * x - y = 0 := by
    rw [abs_eq_zero] at h1
    exact h1
  have hy : y = 2 * x := by linarith
  have h3 : (a - 3 * b) ^ 2 = 0 := by
    linarith [abs_nonneg (2 * x - y), sq_nonneg (a - 3 * b)]
  have ha : a = 3 * b := by
    have h4 : a - 3 * b = 0 := by
      rw [sq_eq_zero_iff] at h3
      exact h3
    linarith
  have num_eq : 2 * a ^ 3 * x ^ 2 + a * b ^ 2 * y ^ 2 + 3 * b ^ 3 * x * y = 72 * b ^ 3 * x ^ 2 := by 
    rw [ha, hy]
    ring
  have denom_eq : 3 * a ^ 3 * x ^ 2 + a * b ^ 2 * y ^ 2 + 2 * b ^ 3 * x * y = 97 * b ^ 3 * x ^ 2 := by 
    rw [ha, hy]
    ring
  rw [num_eq, denom_eq]
  have h4 : 97 * b ^ 3 * x ^ 2 ≠ 0 := by
    intro h5
    have h6 : 3 * a ^ 3 * x ^ 2 + a * b ^ 2 * y ^ 2 + 2 * b ^ 3 * x * y = 0 := by
      rw [denom_eq] at *
      linarith
    have h7 : 3 * a ^ 3 * x ^ 2 + a * b ^ 2 * y ^ 2 + 2 * b ^ 3 * x * y ≠ 0 := m
    contradiction
  field_simp [h4]
  <;> nlinarith