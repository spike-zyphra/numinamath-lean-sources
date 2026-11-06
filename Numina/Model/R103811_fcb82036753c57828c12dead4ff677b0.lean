import Mathlib
open Real

variable (f : ℝ → ℝ)
variable (a b : ℝ)

theorem algebra_2958 {a b : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = a * x ^ 3 + b * x + 1) (h : f 2022 - f (-2022) = 10000) : f 2022 = 5001 := by 
  have h1 : f 2022 = a * 2022 ^ 3 + b * 2022 + 1 := hf 2022
  have h2 : f (-2022) = a * (-2022) ^ 3 + b * (-2022) + 1 := hf (-2022)
  rw [h1, h2] at h 
  have h3 : a * 2022 ^ 3 + b * 2022 = 5000 := by 
    norm_num at h ⊢
    linarith 
  rw [h1]
  linarith [h3]