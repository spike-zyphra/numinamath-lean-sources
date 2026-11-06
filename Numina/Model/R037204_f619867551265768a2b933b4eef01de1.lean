import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_150131 :
  IsLeast {t : ℝ | ∃ x y, t = (y - 1) / (x - 2) ∧ (x + 2) ^ 2 + y ^ 2 = 1} 0 := by
  constructor
  · -- Show 0 is in the set
    use -2, 1
    norm_num
  · -- Show that 0 is the least
    intro t ht
    rcases ht with ⟨x, y, ht_eq, ht_eq1⟩
    have h1 : x ≤ -1 := by
      nlinarith [sq_nonneg (x + 2 - 0), sq_nonneg (y - 0), sq_nonneg (x + 2), sq_nonneg (y), ht_eq1]
    have h2 : x ≥ -3 := by
      nlinarith [sq_nonneg (x + 2 - 0), sq_nonneg (y - 0), sq_nonneg (x + 2), sq_nonneg (y), ht_eq1]
    have h3 : y ≤ 1 := by
      nlinarith [sq_nonneg (x + 2), sq_nonneg (y - 1), sq_nonneg (x + 2 - 0), sq_nonneg (y - 0), ht_eq1]
    have h4 : y ≥ -1 := by
      nlinarith [sq_nonneg (x + 2), sq_nonneg (y + 1), sq_nonneg (x + 2 - 0), sq_nonneg (y - 0), ht_eq1]
    have h5 : x - 2 < 0 := by
      nlinarith
    have h6 : y - 1 ≤ 0 := by
      nlinarith
    have ht_eq2 : (y - 1) / (x - 2) ≥ 0 := by
      apply div_nonneg_of_nonpos
      · -- Show that y - 1 ≤ 0
        linarith
      · -- Show that x - 2 ≤ 0
        linarith
    linarith [ht_eq, ht_eq2]