import Mathlib

theorem algebra_11763 {F : ℝ → ℝ} (k : ℝ) (hF : F = fun d => k / d ^ 2) (h : F 4000 = 600) (d : ℝ) (hd : d = 240000) :
    F d = 1 / 6 := by
  have hk : k = 600 * (4000 : ℝ) ^ 2 := by
    rw [hF] at h
    norm_num at h ⊢
    linarith
  rw [hd]
  rw [hF, hk]
  norm_num