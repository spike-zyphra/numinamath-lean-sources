import Mathlib

theorem algebra_140228 (a b : ℝ × ℝ × ℝ)
    (ha : a = (3, 4, -1)) (hb : b = (1, 1, 0)) :
    (a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2) / (Real.sqrt (b.1^2 + b.2.1^2 + b.2.2^2)) = 7 * Real.sqrt 2 / 2 := by
  rw [ha, hb]
  have h1 : (3 : ℝ) * (1 : ℝ) + (4 : ℝ) * (1 : ℝ) + (-1 : ℝ) * (0 : ℝ) = (7 : ℝ) := by norm_num
  have h2 : Real.sqrt ((1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = Real.sqrt (2 : ℝ) := by norm_num
  rw [h1, h2]
  have h3 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h4 : Real.sqrt 2 > 0 := by positivity
  field_simp [h3, h4]
  <;> ring_nf <;> norm_num [Real.sq_sqrt, h4]
  <;> ring_nf <;> norm_num