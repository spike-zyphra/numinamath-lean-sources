import Mathlib

theorem algebra_264754 (w : ℕ) (hw : 0 < w) (h : w^3 = 9 * w) : w^5 = 243 := by
  have hw2 : w = 3 := by 
    have hw1 : w > 0 := hw
    have eq1 : w ^ 2 = 9 := by
      have hw2 : w ≠ 0 := by linarith
      have eq4 : w * (w ^ 2) = w * 9 := by
        nlinarith [h]
      have : w ^ 2 = 9 := by
        apply (mul_left_inj' hw2).mp
        linarith
      assumption
    have hw2 : w ≤ 3 := by nlinarith
    interval_cases w <;> omega
  calc
    w ^ 5 = 3 ^ 5 := by rw [hw2]
    _ = 243 := by norm_num