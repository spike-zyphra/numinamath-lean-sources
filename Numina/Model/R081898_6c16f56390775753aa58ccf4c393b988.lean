import Mathlib

theorem algebra_196412 {f : ℝ → ℝ} (hpos : ∀ x y, 0 < x → 0 < y → f (x * y) = f x + f y)
    (hf2 : f 2 = 1) : f (1 / 64) = -6 := by

  -- show f 4 = 2
  have hf4 : f 4 = 2 := by
    have h1 := hpos 2 2 (by norm_num) (by norm_num)
    norm_num at h1
    rw [hf2] at h1
    linarith

  -- show f 8 = 3
  have hf8 : f 8 = 3 := by
    have h1 := hpos 4 2 (by norm_num) (by norm_num)
    norm_num at h1
    rw [hf4] at h1
    linarith

  -- show f 16 = 4
  have hf16 : f 16 = 4 := by
    have h1 := hpos 8 2 (by norm_num) (by norm_num)
    norm_num at h1
    rw [hf8] at h1
    linarith

  -- show f 32 = 5
  have hf32 : f 32 = 5 := by
    have h1 := hpos 16 2 (by norm_num) (by norm_num)
    norm_num at h1
    rw [hf16] at h1
    linarith

  -- show f 64 = 6
  have hf64 : f 64 = 6 := by
    have h1 := hpos 32 2 (by norm_num) (by norm_num)
    norm_num at h1
    rw [hf32] at h1
    linarith

  -- show f 1 = 0
  have hf1 : f 1 = 0 := by
    have h1 := hpos 1 1 (by norm_num) (by norm_num)
    norm_num at h1 ⊢
    linarith

  -- relate f(1/64) and f(64)
  have h1_64 : f (1 / 64 * 64) = f (1 / 64) + f 64 := hpos (1 / 64) 64 (by norm_num) (by norm_num)
  norm_num at h1_64 ⊢
  rw [hf64] at h1_64
  rw [hf1] at h1_64
  linarith