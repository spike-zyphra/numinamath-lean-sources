import Mathlib

theorem algebra_15508 {l h d : ℝ} (hl : l > 0) (hh : h > 0)
    (hd : d > 0) (h1 : l / h = 4 / 3) (h2 : l^2 + h^2 = d^2) (h3 : d = 27) :
    l = 21.6 := by
  have h4 : h ≠ 0 := by
    linarith
  have h5 : l = 4 / 3 * h := by
    field_simp [h4] at h1
    linarith
  have h6 : d ^ 2 = 27 ^ 2 := by
    rw [h3]
  rw [h6] at h2
  rw [h5] at h2
  have h7 : h ^ 2 = (6561 / 25 : ℝ) := by
    nlinarith
  have h8 : h = (81 / 5 : ℝ) := by
    nlinarith [sq_nonneg h, hh]
  have h9 : l = (108 / 5 : ℝ) := by
    rw [h8] at h5
    nlinarith
  rw [h9]
  norm_num