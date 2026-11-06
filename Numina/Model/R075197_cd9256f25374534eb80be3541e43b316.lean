import Mathlib

theorem algebra_15749 (x : ℕ) (hx : 2^x + 2^x + 2^x + 2^x = 128) :
    (x + 1) * (x - 1) = 24 := by
  have eq1 : 2^x + 2^x + 2^x + 2^x = 4 * (2^x) := by 
    ring
  rw [eq1] at hx
  have h2 : 2^x = 32 := by 
    omega
  have hx5 : x = 5 := by
    exact Nat.pow_right_injective (by norm_num) h2
  calc
    (x + 1) * (x - 1) = (5 + 1) * (5 - 1) := by rw [hx5]
    _ = 6 * 4 := by norm_num
    _ = 24 := by norm_num