import Mathlib

open Real
open scoped BigOperators

theorem calculus_15864 {a b : ℝ × ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
  (h : abs (a.1 * b.2 - a.2 * b.1) = 8) :
  abs ((2 * a.1 + 3 * b.1) * (a.2 - 5 * b.2) - (2 * a.2 + 3 * b.2) * (a.1 - 5 * b.1)) = 104 := by 
  have h1 : (2 * a.1 + 3 * b.1) * (a.2 - 5 * b.2) - (2 * a.2 + 3 * b.2) * (a.1 - 5 * b.1) = 13 * (a.2 * b.1 - a.1 * b.2) := by 
    ring 
  rw [h1] 
  have h2 : abs (13 * (a.2 * b.1 - a.1 * b.2)) = 13 * abs (a.2 * b.1 - a.1 * b.2) := by 
    rw [abs_mul]
    norm_num 
  rw [h2]
  have h3 : abs (a.2 * b.1 - a.1 * b.2) = abs (a.1 * b.2 - a.2 * b.1) := by 
    have h3 : a.2 * b.1 - a.1 * b.2 = - (a.1 * b.2 - a.2 * b.1) := by 
      ring 
    rw [h3] 
    rw [abs_neg]
  rw [h3] 
  rw [h] 
  all_goals norm_num