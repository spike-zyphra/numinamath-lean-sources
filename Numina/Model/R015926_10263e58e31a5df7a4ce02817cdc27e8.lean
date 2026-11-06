import Mathlib

theorem algebra_317372 {x y z : ℕ} (h₀ : x + y = z - 6) (h₁ : y + z = x + 16)
    (h₂ : z + x = y + 8) : x * y * z = 60 := by
  have h3 : z ≥ 6 := by
    omega
  have h4 : z = x + y + 6 := by 
    omega
  have h5 : y = 5 := by 
    rw [h4] at h₁
    omega
  have h6 : z = x + 11 := by
    rw [h5] at h4
    omega
  have h7 : x = 1 := by 
    rw [h6, h5] at h₂
    omega
  have h8 : z = 12 := by
    omega
  calc
    x * y * z = 1 * 5 * 12 := by rw [h7, h5, h8]
    _ = 60 := by norm_num