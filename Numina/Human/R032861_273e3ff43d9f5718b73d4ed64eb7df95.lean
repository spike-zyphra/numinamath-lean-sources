import Mathlib

theorem algebra_122063 {x : ℝ} (hx : x > 0) (h : x - √(2022 / x) = 2023) :
    x - √(2022 * x) + 2023 = 2024 := by
  field_simp at h
  rw [Real.sqrt_mul (by simp)]
  nth_rw 1 [show x = √x ^ 2 by simp [le_of_lt hx]] at h ⊢
  rw [show 2023 = √2022 ^ 2 + 1 by norm_num] at h
  replace h : (√x ^ 2 - √2022 * √x - 1) * (√x + √2022) = 0 := by linear_combination h
  simp [show √x + √2022 ≠ 0 by positivity] at h
  linear_combination h
