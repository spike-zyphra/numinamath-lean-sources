import Mathlib

theorem algebra_277237 {x : ℝ} (hx : (x - 2) * (x + 2) = 2021) : (x - 1) * (x + 1) = 2024 := by
  have h1 : x^2 = 2025 := by
    nlinarith
  calc
    (x - 1) * (x + 1) = x^2 - 1 := by ring
    _ = 2025 - 1 := by rw [h1]
    _ = 2024 := by norm_num