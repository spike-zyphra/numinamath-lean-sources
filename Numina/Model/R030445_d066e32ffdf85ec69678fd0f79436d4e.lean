import Mathlib
theorem algebra_611055 (f : ℝ → ℝ) (hf : ∀ a b n : ℕ, a > 0 → b > 0 → n > 0 → a + b = 2 ^ n → f a + f b = n ^ 2) : f 2002 = 96:= by
  have h1 := hf 2 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf2 : f 2 = 2 := by
    norm_num at h1
    linarith
  have h2 := hf 14 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf14 : f 14 = 14 := by
    norm_num [hf2] at h2
    linarith
  have h3 := hf 18 14 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf18 : f 18 = 11 := by
    norm_num [hf14] at h3
    linarith
  have h4 := hf 46 18 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hf46 : f 46 = 25 := by
    norm_num [hf18] at h4
    linarith
  have h5 := hf 2002 46 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [hf46] at h5
  linarith