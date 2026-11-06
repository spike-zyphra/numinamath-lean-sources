import Mathlib

theorem algebra_237033 {f : ℝ → ℝ} (hpos : ∀ x, 0 < x → 0 < f x)
    (hf1 : f 1 = 1) (hadd : ∀ a b, f (a + b) * (f a + f b) = 2 * f a * f b + a ^ 2 + b ^ 2) :
    f 2019 = 2019 := by

  have h0 : f 0 = 0 := by
    have h1_0 : f (1 + 0) * (f 1 + f 0) = 2 * f 1 * f 0 + 1 ^ 2 + (0 : ℝ) ^ 2 := by 
      specialize hadd 1 0
      simpa using hadd
    rw [show (1 + (0 : ℝ) : ℝ) = (1 : ℝ) by ring] at h1_0
    rw [hf1] at h1_0
    nlinarith 
  have hfx (x : ℝ) (hx : 0 < x) : f x = x := by
    have h1 : f (x + (0 : ℝ)) * (f x + f 0) = 2 * f x * f 0 + x ^ 2 + (0 : ℝ) ^ 2 := by 
      specialize hadd x 0
      simpa using hadd
    have h2 : f 0 = 0 := h0
    rw [show x + (0 : ℝ) = x by ring] at h1
    rw [h2] at h1 
    have h4 : f x > 0 := hpos x hx
    nlinarith [sq_pos_of_pos hx, sq_nonneg (f x - x)]
  
  specialize hfx 2019 (by norm_num)
  linarith