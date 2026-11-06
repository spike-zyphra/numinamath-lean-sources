import Mathlib

theorem algebra_3147 (x y : ℝ) (h1 : (2 : ℝ)^(3 * x - 5 * y) = 2048) (h2 : (3 : ℝ)^(x - 2 * y) = 27) :
    (4 : ℝ)^(x - y) = 1024 := by
  have eq1 : 3 * x - 5 * y = 11 := by
    have h3 : (2 : ℝ) ^ (3 * x - 5 * y) = 2048 := h1
    have h4 : (2048 : ℝ) = 2 ^ (11 : ℝ) := by norm_num
    rw [h4] at h3
    have h5 : (3 * x - 5 * y) = (11 : ℝ) := by
      apply_fun (Real.logb 2) at h3
      simp at h3
      linarith
    linarith

  have eq2 : x - 2 * y = 3 := by
    have h6 : (3 : ℝ) ^ (x - 2 * y) = 27 := h2
    have h7 : (27 : ℝ) = 3 ^ (3 : ℝ) := by norm_num
    rw [h7] at h6
    have h8 : (x - 2 * y) = (3 : ℝ) := by
      apply_fun (Real.logb 3) at h6
      simp at h6
      linarith
    linarith

  have hx : x = 7 := by
    linarith [eq1, eq2]

  have hy : y = 2 := by
    linarith [eq1, eq2]

  rw [hx, hy]
  norm_num