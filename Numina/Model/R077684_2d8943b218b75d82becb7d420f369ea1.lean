import Mathlib

theorem inequalities_107454 (a b c d e : ℝ) (h : a + b + c + d + e = 0)
    (A B : ℝ) (hA : A = a * b + b * c + c * d + d * e + e * a)
    (hB : B = a * c + c * e + e * b + b * d + d * a) :
    2005 * A + B ≤ 0 ∨ A + 2005 * B ≤ 0 := by
  have h1 : (a + b + c + d + e) ^ 2 = 0 := by 
    rw [h]
    norm_num
  have h2 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = -2 * (A + B) := by
    have eq1 : (a + b + c + d + e) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + 2 * (A + B) := by
      rw [hA, hB]
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d, sq_nonneg e, sq_nonneg (a + b + c + d + e)]
    nlinarith [h1, eq1, sq_nonneg (a + b + c + d + e)]
  have h3 : A + B ≤ 0 := by
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d, sq_nonneg e, h2]
  by_contra h4
  push_neg at h4
  have h4_1 : 2005 * A + B > 0 := by
    linarith [h4.1]
  have h4_2 : A + 2005 * B > 0 := by
    linarith [h4.2]
  have h5 : A + B > 0 := by
    nlinarith [h4_1, h4_2]
  linarith [h3, h5]