import Mathlib

open Finset

theorem algebra_280272 {θ : ℤ → ℚ} (hθ : ∀ a, θ a = 1 / (a ^ 2 - 1)) :
    (θ 3 + θ 5 + θ 7 + θ 9 + θ 11).num + (θ 3 + θ 5 + θ 7 + θ 9 + θ 11).den = 29 := by 
  have h3_val : θ 3 = (1 / 8 : ℚ) := by 
    rw [hθ]
    norm_num
  have h5_val : θ 5 = (1 / 24 : ℚ) := by 
    rw [hθ]
    norm_num
  have h7_val : θ 7 = (1 / 48 : ℚ) := by 
    rw [hθ]
    norm_num
  have h9_val : θ 9 = (1 / 80 : ℚ) := by 
    rw [hθ]
    norm_num
  have h11_val : θ 11 = (1 / 120 : ℚ) := by 
    rw [hθ]
    norm_num

  have h_sum : θ 3 + θ 5 + θ 7 + θ 9 + θ 11 = (5 / 24 : ℚ) := by 
    rw [h3_val, h5_val, h7_val, h9_val, h11_val]
    norm_num

  rw [h_sum]
  norm_num