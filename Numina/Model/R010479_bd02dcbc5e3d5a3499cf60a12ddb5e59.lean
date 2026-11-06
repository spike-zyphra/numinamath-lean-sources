import Mathlib

theorem algebra_13145 : IsLeast {n : ℕ | Finset.sum (Finset.range n) (fun i => 2 ^ i) > 200} 8 := by
  constructor
  · -- First, show 8 is indeed in the set.
    show Finset.sum (Finset.range 8) (fun i => 2 ^ i) > 200
    norm_num [Finset.sum_range_succ]
  · -- Now, prove that 8 is the least such.
    intro n hn
    have h : Finset.sum (Finset.range n) (fun i => 2 ^ i) > 200 := by
      simpa using hn
    by_contra h'
    push_neg at h'
    -- We need to prove n ≥ 8 by showing contradiction if n < 8.
    -- Lean's way: case analysis.
    interval_cases n <;> norm_num [Finset.sum_range_succ] at h <;> omega