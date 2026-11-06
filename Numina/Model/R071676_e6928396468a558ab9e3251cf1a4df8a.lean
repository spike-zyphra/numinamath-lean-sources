import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_291267 :
  IsGreatest {t : ℝ | ∃ x y z, 0 ≤ x ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = 1 ∧ t = (x - y * z)^2 + (y - z * x)^2 + (z - x * y)^2} 1 := by
  constructor
  · -- Show that 1 belongs to the set
    use 0, 0, 1
    norm_num
  · -- Show that for all t in the set, t ≤ 1
    intro t ht
    rcases ht with ⟨x, y, z, h0, h1, h2, h3, ht⟩
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x - 0), sq_nonneg (y - x), sq_nonneg (z - y),
      mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y - x by linarith),
      mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ z - y by linarith),
      mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ 1 - z by nlinarith)]