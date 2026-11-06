import Mathlib

theorem algebra_129028 (k s : ℕ) (h₀ : k = s / 3) (h₁ : s = (k + s) / 2)
    (h₂ : s > 0) (h₃ : k > 0) :
    k / s = 16 := by 
  have h4 : 2 * s = k + s := by 
    omega
  have h5 : s = k := by 
    omega
  have h6 : k = 0 := by
    rw [show s = k by omega] at h₀
    omega
  omega