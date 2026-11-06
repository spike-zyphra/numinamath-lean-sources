import Mathlib

theorem algebra_20347 (d1 d2 v1 v2 : ℝ) (h1 : d1 = 9 + 12) (h2 : d2 = √(9^2 + 12^2)) (t1 : ℝ)
    (h3 : v1 = 42) (t2 : ℝ) (h4 : v2 = 45) (h5 : t1 = d1 / v1) (h6 : t2 = d2 / v2)
    : (t1 - t2) * 60 = 10 := by
  have hd1 : d1 = 21 := by
    rw [h1]
    norm_num

  have hd2 : d2 = 15 := by
    rw [h2]
    have h225 : (9 : ℝ) ^ 2 + (12 : ℝ) ^ 2 = 225 := by norm_num
    rw [h225]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

  have ht1 : t1 = (21 : ℝ) / 42 := by
    rw [h5, hd1, h3]

  have ht2 : t2 = (15 : ℝ) / 45 := by
    rw [h6, hd2, h4]

  rw [ht1, ht2]
  norm_num