import Mathlib

open Real

theorem inequalities_598035 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    sqrt (13 * a + 1) + sqrt (13 * b + 1) + sqrt (13 * c + 1) ≤ 4 * sqrt 3 := by
  have h2 : (sqrt (13 * a + 1) + sqrt (13 * b + 1) + sqrt (13 * c + 1)) ^ 2 ≤ 48 := by
    have h3 : (sqrt (13 * a + 1) + sqrt (13 * b + 1) + sqrt (13 * c + 1)) ^ 2 ≤ 3 * ((13 * a + 1) + (13 * b + 1) + (13 * c + 1)) := by
      nlinarith [sq_nonneg (sqrt (13 * a + 1) - sqrt (13 * b + 1)), sq_nonneg (sqrt (13 * b + 1) - sqrt (13 * c + 1)), sq_nonneg (sqrt (13 * c + 1) - sqrt (13 * a + 1)),
        Real.sqrt_nonneg (13 * a + 1), Real.sqrt_nonneg (13 * b + 1), Real.sqrt_nonneg (13 * c + 1),
        Real.sq_sqrt (show 0 ≤ (13 * a + 1 : ℝ) by nlinarith), Real.sq_sqrt (show 0 ≤ (13 * b + 1 : ℝ) by nlinarith), Real.sq_sqrt (show 0 ≤ (13 * c + 1 : ℝ) by nlinarith)]
    have h4 : (13 * a + 1) + (13 * b + 1) + (13 * c + 1) = 16 := by
      nlinarith [h]
    nlinarith [h4]
  have h5 : sqrt 48 = 4 * sqrt 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h6 : (sqrt (13 * a + 1) + sqrt (13 * b + 1) + sqrt (13 * c + 1)) ≤ sqrt 48 := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [h2]
  linarith [h5, h6]