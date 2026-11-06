import Mathlib

open Set Real

theorem inequalities_249609 :
    ∃ a b c d e : ℝ,
      logb (1/6) (a^6 + b^6 + c^6 + d^6 + e^6 + 1) ≥
        logb (1/6) a + logb (1/6) b + logb (1/6) c + logb (1/6) d + logb (1/6) e - 1 := by 
  use 1, 1, 1, 1, 1
  have h1 : logb (1/6) (1^6 + 1^6 + 1^6 + 1^6 + 1^6 + 1) = logb (1/6) 6 := by
    norm_num
  have h2 : logb (1/6) (1 : ℝ) = 0 := by
    simp [logb_one]
  have h3 : logb (1/6) 6 = -1 := by
    rw [logb_eq_iff_rpow_eq] <;> norm_num
  rw [h1]
  have : logb (1/6) (6 : ℝ) ≥ (0 + 0 + 0 + 0 + 0) - 1 := by 
    rw [h3]
    linarith
  linarith [h2]