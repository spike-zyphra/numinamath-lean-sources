import Mathlib

theorem algebra_167469 (x : ℕ) (hx : x ≠ 0) (h : 2^10 = x) :
    ∃ n, 2^n = x / 2 := by 
  have hx_eq : x = 2^10 := by 
    omega
  use 9
  calc
    2 ^ 9 = (2 ^ 10) / 2 := by norm_num
    _ = x / 2 := by rw [hx_eq]