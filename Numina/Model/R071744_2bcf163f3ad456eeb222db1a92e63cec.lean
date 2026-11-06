import Mathlib

theorem algebra_170152 {d : ℕ} (hd : d > 0) (h : (2 * d - 1024) * 2 ^ 9 = d) :
    d ≥ 1023 := by 
  omega