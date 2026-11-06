import Mathlib

theorem number_theory_628031 (n : ℕ) (h : n = 48^(2022)) :
    (n % 7 = 1) := by 
  rw [h]
  norm_num