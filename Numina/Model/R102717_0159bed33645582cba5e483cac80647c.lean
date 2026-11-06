import Mathlib

open Real

theorem algebra_15406 :
    IsGreatest {t : ℝ | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 1 ∧ t = x + y ^ 2 + z ^ 3} 1 := by
  constructor
  · -- Show that 1 is in the set
    use 1, 0, 0
    norm_num
  · -- Show that any element in the set is ≤ 1
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, h_eq1, ht⟩
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
      sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), 
      sq_nonneg (y - z), sq_nonneg (x - y), sq_nonneg (x - z)]