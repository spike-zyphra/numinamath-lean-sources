import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_59995 :
  IsGreatest {z : ℝ | ∃ x y, z = (x + y) / x ∧ -4 ≤ x ∧ x ≤ -2 ∧ 2 ≤ y ∧ y ≤ 4} (1 / 2) := by
  constructor
  · -- First, we'll show that 1/2 is achievable with x = -4 and y = 2
    use -4, 2
    norm_num
    all_goals norm_num
  · -- Now, we need to show that for any z in the set, z ≤ 1/2
    intro z h
    rcases h with ⟨x, y, hz, hx1, hx2, hy1, hy2⟩
    have h1 : z = (x + y) / x := hz
    have hx2_neg : x < 0 := by linarith [hx1, hx2]

    have h2 : z ≤ 1 / 2 := by
      rw [h1]
      apply (div_le_iff_of_neg' (by linarith)).mpr
      linarith [sq_nonneg (x + 4), sq_nonneg (y - 2)]
      all_goals linarith
      all_goals linarith
    linarith
    all_goals linarith
    all_goals nlinarith
    all_goals linarith