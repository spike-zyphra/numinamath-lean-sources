import Mathlib

theorem number_theory_14345 (x : ℕ) (hx : x > 0) (h : 9 * x ≡ 1 [MOD 25]) :
    (11 + x) % 25 = 0 := by 
  norm_num [Nat.ModEq] at h 
  omega