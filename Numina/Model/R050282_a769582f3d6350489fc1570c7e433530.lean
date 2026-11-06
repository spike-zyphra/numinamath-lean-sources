import Mathlib

theorem algebra_158943 (n : ℕ) (hn : n = 41) (D : ℝ) (hD : D = 3) :
    (D * n) / (n - 1) = 3.075 := by 
  rw [hn, hD]
  norm_num