import Mathlib

theorem algebra_234162 {x y : ℝ} (h₁ : x - y = 6) (h₂ : x ^ 2 + y ^ 2 = 22) :
    x ^ 3 - y ^ 3 = 90 := by 
  have h₃ : (x - y) ^ 2 = 36 := by
    rw [h₁]
    norm_num
  have h₄ : (x - y) ^ 2 = (x ^ 2 + y ^ 2) - 2 * (x * y) := by 
    ring_nf
  rw [h₁, h₂] at h₄
  have h₅ : x * y = -7 := by
    linarith
  have h₆ : x ^ 3 - y ^ 3 = (x - y) * ((x ^ 2 + y ^ 2) + (x * y)) := by 
    ring 
  rw [h₆, h₁, h₂, h₅]
  norm_num