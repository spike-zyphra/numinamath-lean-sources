import Mathlib

theorem number_theory_276265 {N : ℕ} (hN : N % 60 = 49) :
    N % 15 = 4 := by 
  have h1 : N % 60 = 49 := hN
  have h2 : N % 15 = 49 % 15 := by 
    omega 
  calc 
    N % 15 = 49 % 15 := h2
    _ = 4 := by norm_num