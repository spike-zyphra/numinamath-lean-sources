import Mathlib

theorem algebra_302922 {m n a : ℝ} (ha : 0 < a) (h1 : 16^(9*m) = a) (h2 : 4^(37*n) = 1/a) :
    (36*m + 74*n - 1)^2000 = 1 := by
  have h3 : (16 : ℝ) ^ (9 * m) = 2 ^ (36 * m) := by
    calc
      (16 : ℝ) ^ (9 * m)
          = (2 ^ (4 : ℝ)) ^ (9 * m) := by norm_num
      _ = 2 ^ ((4 : ℝ) * (9 * m)) := by rw [← Real.rpow_mul]; all_goals norm_num
      _ = 2 ^ (36 * m) := by ring_nf
  have h4 : (4 : ℝ) ^ (37 * n) = 2 ^ (74 * n) := by
    calc
      (4 : ℝ) ^ (37 * n)
          = (2 ^ (2 : ℝ)) ^ (37 * n) := by norm_num
      _ = 2 ^ ((2 : ℝ) * (37 * n)) := by rw [← Real.rpow_mul]; all_goals norm_num
      _ = 2 ^ (74 * n) := by ring_nf
  rw [h3] at h1
  rw [h4] at h2
  have h5 : (2 : ℝ) ^ (36 * m + 74 * n) = 1 := by
    have : (2 : ℝ) ^ (36 * m + 74 * n) = (2 ^ (36 * m)) * (2 ^ (74 * n)) := by
      rw [Real.rpow_add]; all_goals linarith
    rw [this, h1, h2]
    field_simp
    all_goals linarith
  have h6 : 36 * m + 74 * n = 0 := by
    have h7 : (2 : ℝ) ^ (36 * m + 74 * n) = (2 : ℝ) ^ (0 : ℝ) := by
      rw [h5, Real.rpow_zero]
    have h7' : 36 * m + 74 * n = (0 : ℝ) := by
      apply_fun (Real.logb 2) at h7
      simp at h7 ⊢
      all_goals linarith
    linarith
  have h8 : 36 * m + 74 * n - 1 = -1 := by linarith
  rw [h8]
  norm_num