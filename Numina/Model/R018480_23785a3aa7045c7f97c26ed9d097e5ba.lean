import Mathlib

theorem algebra_278443 (L : ℝ) (hL : L = 600) (α : ℝ) (hα : α = Real.pi / 6)
    (V : ℝ) (hV : V > 0) (h : L * (4 / 16) = V * (2 * Real.pi / 3) ^ 2 + 10 * (L * (1 / 4)) ^ 2) :
    round V = 49 := by
  rw [hL] at h
  have h1 : (600 : ℝ) * (4 / 16 : ℝ) = 150 := by norm_num
  have h2 : (600 : ℝ) * (1 / 4 : ℝ) = (150 : ℝ) := by norm_num
  have h3 : 10 * ((600 : ℝ) * (1 / 4 : ℝ)) ^ 2 = (225000 : ℝ) := by
    rw [h2]
    norm_num
  rw [h1, h3] at h
  have h4 : V * (2 * Real.pi / 3) ^ 2 < 0 := by nlinarith
  have h5 : (2 * Real.pi / 3) ^ 2 > 0 := by
    positivity
  have h6 : V < 0 := by
    nlinarith [h5, h4, sq_nonneg (V) ]
  linarith -- contradicts $V > 0$