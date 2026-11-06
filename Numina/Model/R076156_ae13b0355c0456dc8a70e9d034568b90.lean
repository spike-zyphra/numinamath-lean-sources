import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_316859 :
  IsLeast {t : ℝ | ∃ x y : ℝ, x > 1 ∧ y > 1 ∧ x * y - 2 * x - y + 1 = 0 ∧ t = 3 / 2 * x ^ 2 + y ^ 2} 15 := by
  constructor
  · -- Show 15 is achievable, using x = 2, y = 3.
    use 2, 3
    norm_num
  · -- Show that all elements in the set are ≥ 15
    intro t ht
    rcases ht with ⟨x, y, hx, hy, h_eq, ht_eq⟩
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 3), sq_nonneg (x - 2 - (y - 3)), mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy)]