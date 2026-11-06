import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_21969 :
  IsGreatest {y | ∃ x : ℝ, x ∈ Icc 0 1 ∧ y = x * (1 - x)^5} (3125/46656) := by
  constructor
  · -- Show that 3125/46656 is in the set
    use 1 / 6
    constructor
    · -- Show that 1/6 is in [0, 1]
      exact ⟨by norm_num, by norm_num⟩
    · -- Show that 3125/46656 = (1/6) * (1 - 1/6)^5
      norm_num
  · -- Show that 3125/46656 is greatest in the set
    intro y hy
    rcases hy with ⟨x, hx, h_eq⟩
    rw [h_eq]
    rcases hx with ⟨hx0, hx1⟩
    have h2 : x * (1 - x)^5 ≤ 3125 / 46656 := by
      have h3 : x * (1 - x)^5 - 3125 / 46656 ≤ 0 := by
        have h4 : x ≥ 0 := by linarith
        have h5 : x ≤ 1 := by linarith
        nlinarith [sq_nonneg (x - 1 / 6), sq_nonneg ((x - 1 / 6) * (x - 1)), sq_nonneg (x * (x - 1 / 6)), sq_nonneg ((1 - x) * (x - 1 / 6)), sq_nonneg ((x - 1 / 6) * (x)), sq_nonneg ((x - 1 / 6) * ((1 - x))), sq_nonneg ((x - 1 / 6) * (x ^ 2)), sq_nonneg ((x - 1 / 6) * ((1 - x) ^ 2)), mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ 1 - x by linarith), sq_nonneg (x - 1 / 6), sq_nonneg ((x - 1 / 6) * (x * (1 - x))), sq_nonneg (x * (1 - x)), sq_nonneg (x - 1), sq_nonneg ((x) ^ 2 - (x/6)), sq_nonneg ((1 - x) * (1 - x))]
      linarith
    linarith