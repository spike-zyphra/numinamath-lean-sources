import Mathlib

theorem algebra_10320 {b : ℝ} (p q : ℝ → ℝ) (hp : p = fun x => 2 * x - 7) (hq : q = fun x => 3 * x - b)
    (h : p (q 4) = 7) : b = 5 := by
  have q4 : q 4 = 3 * 4 - b := by 
    rw [hq]
  have pq4 : p (q 4) = 2 * (3 * 4 - b) - 7 := by
    rw [q4]
    rw [hp]
  rw [pq4] at h
  norm_num at h 
  linarith