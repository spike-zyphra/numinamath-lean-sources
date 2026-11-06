import Mathlib

theorem algebra_238805 {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) (hpos : ∀ x > 0, f (2 + x) = -2 * f (2 - x)) (hf1 : f (-1) = 4) : f (-3) = -8 := by
  have h1 : f 1 = 4 := by
    have h_even := hf 1
    linarith [hf1, h_even]
  have h2 : f 3 = -8 := by
    specialize hpos 1 (by norm_num)
    rw [show (2 + (1 : ℝ) : ℝ) = (3 : ℝ) by norm_num, show (2 - (1 : ℝ) : ℝ) = (1 : ℝ) by norm_num] at hpos
    rw [h1] at hpos
    linarith
  have h3 : f (-3) = f 3 := by 
    apply hf
  rw [h3]
  linarith [h2]