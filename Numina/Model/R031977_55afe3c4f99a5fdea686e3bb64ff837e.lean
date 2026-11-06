import Mathlib


lemma lemma_1 {a b z : ℝ} (hz : z = 2 * (a + 2 * b)) (h : 4 * z ^ 2 + 2 * a * z - 8 * b * (9 * a + 4) = 0) :
    9 * a ^ 2 + (4 - 4 * z) * a + z ^ 2 - 2 * z = 0 := by
  have h1 : b = (z - 2 * a) / 4 := by
    linarith [hz]
  rw [h1] at h
  nlinarith [sq_nonneg (z - 2 * a), sq_nonneg (a - z / 2 + 2 / 9), sq_nonneg (a * z - z ^ 2), sq_nonneg (z - 2), sq_nonneg (a * 2 - z)]


theorem algebra_297104 (a b : ℝ) (z : ℝ) (h : 4 * z ^ 2 + (2 * a + Complex.I) * z - 8 * b * (9 * a + 4) - 2 * (a + 2 * b) * Complex.I = 0) :
    z ≤ 3 * Real.sqrt 5 / 5 + 1 := by
  have eq1 := congr_arg Complex.re h
  have eq2 := congr_arg Complex.im h
  simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_add, mul_comm, mul_assoc] at eq1 eq2
  have h1 : z = 2 * (a + 2 * b) := by
    nlinarith
  have h2 : 4 * z ^ 2 + 2 * a * z - 8 * b * (9 * a + 4) = 0 := by
    nlinarith
  have h3 : 9 * a ^ 2 + (4 - 4 * z) * a + z ^ 2 - 2 * z = 0 := by
    have hz : z = 2 * (a + 2 * b) := h1
    have h_eq : 4 * z ^ 2 + 2 * a * z - 8 * b * (9 * a + 4) = 0 := h2
    apply lemma_1 (hz) (h_eq)
  nlinarith [sq_nonneg (a + (4 - 4 * z) / 18 ), sq_nonneg (z - (1 + 3 * Real.sqrt 5 / 5)), sq_nonneg (z - (1 - 3 * Real.sqrt 5 / 5)), Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]