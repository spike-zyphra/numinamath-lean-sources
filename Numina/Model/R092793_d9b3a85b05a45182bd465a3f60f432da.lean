import Mathlib

theorem algebra_96478 {f : ℂ → ℂ} (hf : ∀ x, f x = (x ^ 4 + x ^ 2) / (x + 1)) :
    f Complex.I = 0 := by 
  have h_eq : f Complex.I = (Complex.I ^ 4 + Complex.I ^ 2) / (Complex.I + 1) := hf Complex.I
  rw [h_eq]
  have h1 : Complex.I ^ 2 = -1 := by 
    simp [Complex.I_sq]
  have h2 : Complex.I ^ 4 = 1 := by 
    calc 
      Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
      _ = (-1) ^ 2 := by rw [h1]
      _ = 1 := by norm_num
  have num_eq_zero : Complex.I ^ 4 + Complex.I ^ 2 = 0 := by
    rw [h2, h1]
    ring
  rw [num_eq_zero]
  all_goals norm_num