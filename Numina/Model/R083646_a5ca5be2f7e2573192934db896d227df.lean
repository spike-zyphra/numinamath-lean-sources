import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_194100 :
  IsGreatest {t : ℝ | ∃ x y : ℝ, x ∈ Icc 0 1 ∧ y ∈ Icc 0 1 ∧ t = x * y * (x - y)} 0.25 := by
  constructor
  · -- Show that 0.25 can be attained
    use 1, 0.5
    constructor
    · -- Show that 1 is in [0, 1]
      norm_num [mem_Icc]
    constructor
    · -- Show that 0.5 is in [0, 1]
      norm_num [mem_Icc]
    · -- Show that 0.25 is achieved
      norm_num
  · -- Show that any element in the set is ≤ 0.25
    intro t ht
    rcases ht with ⟨x, y, hx, hy, heq⟩
    rw [mem_Icc] at hx hy
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩
    nlinarith [sq_nonneg (x - 0.5), sq_nonneg (y - 0.5), sq_nonneg (x - y), sq_nonneg (x * y - 0.25), sq_nonneg (x * (1 - y) - 0.25), sq_nonneg (y * (1 - x) - 0.25), mul_nonneg (show 0 ≤ 1 - x by linarith [hx2]) (show 0 ≤ 1 - y by linarith [hy2]), mul_nonneg (show 0 ≤ (x) by linarith [hx1]) (show 0 ≤ (y) by linarith [hy1]), mul_nonneg (show 0 ≤ 1 - x by linarith [hx2]) (show 0 ≤ (y) by linarith [hy1]), mul_nonneg (show 0 ≤ (x) by linarith [hx1]) (show 0 ≤ 1 - y by linarith [hy2]), mul_nonneg (show 0 ≤ (x - 0) by linarith [hx1]) (show 0 ≤ (y - 0) by linarith [hy1]), mul_nonneg (show 0 ≤ (x - 0) by linarith [hx1]) (show 0 ≤ (1 - y) by linarith [hy2]), mul_nonneg (show 0 ≤ (1 - x) by linarith [hx2]) (show 0 ≤ (y - 0) by linarith [hy1]), sq_nonneg (x - 0.25), sq_nonneg (y - 0.75)]