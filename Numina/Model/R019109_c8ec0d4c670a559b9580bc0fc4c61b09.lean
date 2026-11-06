import Mathlib

theorem algebra_325767 {x1 x2 k : ℝ} (hx1 : x1^2 + k * x1 + (3 / 4) * k^2 - 3 * k + (9 / 2) = 0)
    (hx2 : x2^2 + k * x2 + (3 / 4) * k^2 - 3 * k + (9 / 2) = 0) :
    x1 ^ 2011 / x2 ^ 2012 = -2 / 3 := by
  have h1 : (k - 3) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x1 + 3 / 2), sq_nonneg (x2 + 3 / 2), sq_nonneg (k - 3), sq_nonneg (x1 - x2)]
  have hk : k = 3 := by nlinarith
  have h11 : x1 = -3 / 2 := by
    rw [hk] at hx1
    have h11 : x1^2 + 3 * x1 + 9 / 4 = 0 := by nlinarith
    have h12 : (x1 + 3 / 2) ^ 2 = 0 := by nlinarith
    have h13 : x1 + 3 / 2 = 0 := by
      apply pow_eq_zero 
      exact h12
    linarith
  have h12 : x2 = -3 / 2 := by
    rw [hk] at hx2
    have h12 : x2^2 + 3 * x2 + 9 / 4 = 0 := by nlinarith
    have h13 : (x2 + 3 / 2) ^ 2 = 0 := by nlinarith
    have h14 : x2 + 3 / 2 = 0 := by
      apply pow_eq_zero 
      exact h13
    linarith
  rw [h11, h12]
  norm_num
  <;> field_simp
  <;> norm_num
  <;> ring_nf