import Mathlib

theorem algebra_222159 : (Nat.floor ((1.0025 : ℝ)^10 * 100000)) % 10 = 8 := by
  have h1 : Nat.floor ((1.0025 : ℝ)^10 * 100000) = 102528 := by
    norm_num [Nat.floor_eq_iff]
  calc 
    (Nat.floor ((1.0025 : ℝ)^10 * 100000)) % 10 = 102528 % 10 := by
      rw [h1]
    _ = 8 := by norm_num