import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_78398 :
  IsGreatest {y : ℝ | ∃ x, y = 1 / (|x + 3| + |x + 1| + |x - 2| + |x - 5|)} (1 / 11) := by
  constructor
  · -- Show 1/11 is in the set
    use 0
    norm_num [abs_of_nonneg, abs_of_nonpos]
    all_goals norm_num
  · -- Show 1/11 is the greatest
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : 1 / (|x + 3| + |x + 1| + |x - 2| + |x - 5|) ≤ 1 / 11 := by
      have h2 : |x + 3| + |x + 1| + |x - 2| + |x - 5| ≥ 11 := by
        have h4 : |x + 3| + |x - 5| ≥ 8 := by
          have h5 : |x + 3| + |x - 5| ≥ |(x + 3) - (x - 5)| := by
            apply abs_sub
          have h6 : |(x + 3) - (x - 5)| = 8 := by
            have h7 : (x + 3) - (x - 5) = 8 := by
              linarith
            rw [h7]
            norm_num
          linarith [h5, h6]
        have h8 : |x + 1| + |x - 2| ≥ 3 := by
          have h9 : |x + 1| + |x - 2| ≥ |(x + 1) - (x - 2)| := by
            apply abs_sub
          have h10 : |(x + 1) - (x - 2)| = 3 := by
            have h11 : (x + 1) - (x - 2) = 3 := by
              linarith
            rw [h11]
            norm_num
          linarith [h9, h10]
        linarith [h4, h8]
      have h3 : 0 < |x + 3| + |x + 1| + |x - 2| + |x - 5| := by
        have h4 : |x + 3| ≥ 0 := by apply abs_nonneg
        have h5 : |x + 1| ≥ 0 := by apply abs_nonneg
        have h6 : |x - 2| ≥ 0 := by apply abs_nonneg
        have h7 : |x - 5| ≥ 0 := by apply abs_nonneg
        by_contra h
        push_neg at h
        have h8 : |x + 3| = 0 := by
          linarith [abs_nonneg (x + 3), abs_nonneg (x + 1), abs_nonneg (x - 2), abs_nonneg (x - 5)]
        have h9 : |x + 1| = 0 := by
          linarith [abs_nonneg (x + 3), abs_nonneg (x + 1), abs_nonneg (x - 2), abs_nonneg (x - 5)]
        have h10 : |x - 2| = 0 := by
          linarith [abs_nonneg (x + 3), abs_nonneg (x + 1), abs_nonneg (x - 2), abs_nonneg (x - 5)]
        have h11 : |x - 5| = 0 := by
          linarith [abs_nonneg (x + 3), abs_nonneg (x + 1), abs_nonneg (x - 2), abs_nonneg (x - 5)]
        have h12 : x + 3 = 0 := by
          rwa [abs_eq_zero] at h8
        have h13 : x + 1 = 0 := by
          rwa [abs_eq_zero] at h9
        have h14 : x - 2 = 0 := by
          rwa [abs_eq_zero] at h10
        have h15 : x - 5 = 0 := by
          rwa [abs_eq_zero] at h11
        linarith [h12, h13, h14, h15]
      have h8 : 1 / (|x + 3| + |x + 1| + |x - 2| + |x - 5|) ≤ 1 / 11 := by
        apply (div_le_div_iff (by linarith) (by linarith)).mpr
        nlinarith [abs_nonneg (x + 3), abs_nonneg (x + 1), abs_nonneg (x - 2), abs_nonneg (x - 5)]
      linarith
    have h4 : 1 / (|x + 3| + |x + 1| + |x - 2| + |x - 5|) ≤ 1 / 11 := h1
    have h5 : y = 1 / (|x + 3| + |x + 1| + |x - 2| + |x - 5|) := by
      linarith [hx]
    linarith [h4, h5]