import Mathlib

open Finset

theorem number_theory_704 : IsLeast { n | ∃a > 0, ∃b > 0, ∃c > 0,
  n = ∑ i ∈ range 9, (a + i) ∧
  n = ∑ i ∈ range 10, (b + i) ∧
  n = ∑ i ∈ range 11, (c + i)
  } 495 := by
  constructor
  · -- Show that 495 is in the set
    use 51, by norm_num, 45, by norm_num, 40, by norm_num
    constructor
    · -- Verify the sum of 9 consecutive integers starting from 51
      norm_num [sum_range_succ]
    constructor
    · -- Verify the sum of 10 consecutive integers starting from 45
      norm_num [sum_range_succ]
    · -- Verify the sum of 11 consecutive integers starting from 40
      norm_num [sum_range_succ]
  · -- Show that 495 is the least element in the set
    intro n hn
    rcases hn with ⟨a, ha, b, hb, c, hc, h9, h10, h11⟩
    norm_num [sum_range_succ] at h9 h10 h11
    omega