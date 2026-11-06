import Mathlib

theorem algebra_275601 (x y z : ℝ) (hx : |x| ≠ 1 / Real.sqrt 3) (hy : |y| ≠ 1 / Real.sqrt 3)
    (hz : |z| ≠ 1 / Real.sqrt 3) (h : x + y + z = x * y * z) :
    (3 * x - x ^ 3) / (1 - 3 * x ^ 2) + (3 * y - y ^ 3) / (1 - 3 * y ^ 2) +
    (3 * z - z ^ 3) / (1 - 3 * z ^ 2) =
    (3 * x - x ^ 3) / (1 - 3 * x ^ 2) * (3 * y - y ^ 3) / (1 - 3 * y ^ 2) *
    (3 * z - z ^ 3) / (1 - 3 * z ^ 2) := by

  have hx2 : 1 - 3 * x^2 ≠ 0 := by
    by_contra h1
    have h2 : x^2 = 1 / 3 := by linarith
    have h4 : |x| = 1 / Real.sqrt 3 := by
      have h5 : |x| = Real.sqrt (x^2) := by 
        rw [Real.sqrt_sq_eq_abs]
      rw [h5]
      rw [show x^2 = (1 / 3 : ℝ) by linarith]
      have h6 : Real.sqrt ((1 / 3 : ℝ)) = 1 / Real.sqrt 3 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      exact_mod_cast h6
    contradiction

  have hy2 : 1 - 3 * y^2 ≠ 0 := by
    by_contra h1
    have h2 : y^2 = 1 / 3 := by linarith
    have h4 : |y| = 1 / Real.sqrt 3 := by
      have h5 : |y| = Real.sqrt (y^2) := by 
        rw [Real.sqrt_sq_eq_abs]
      rw [h5]
      rw [show y^2 = (1 / 3 : ℝ) by linarith]
      have h6 : Real.sqrt ((1 / 3 : ℝ)) = 1 / Real.sqrt 3 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      exact_mod_cast h6
    contradiction

  have hz2 : 1 - 3 * z^2 ≠ 0 := by
    by_contra h1
    have h2 : z^2 = 1 / 3 := by linarith
    have h4 : |z| = 1 / Real.sqrt 3 := by
      have h5 : |z| = Real.sqrt (z^2) := by 
        rw [Real.sqrt_sq_eq_abs]
      rw [h5]
      rw [show z^2 = (1 / 3 : ℝ) by linarith]
      have h6 : Real.sqrt ((1 / 3 : ℝ)) = 1 / Real.sqrt 3 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      exact_mod_cast h6
    contradiction
  field_simp [hx2, hy2, hz2]
  nlinarith [sq_nonneg (x * y + y * z + z * x), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
          sq_nonneg (x * y * z), sq_nonneg (x + y + z - x * y * z), sq_nonneg ((x + y + z)^2 - 3 * (x * y + y * z + z * x)), 
          sq_pos_of_pos (Real.sqrt_pos.mpr (show 0 < (3: ℝ) by norm_num)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ 3), sq_nonneg (x * y), sq_nonneg (x * z), sq_nonneg (y * z)]