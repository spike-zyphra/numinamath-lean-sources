import Mathlib

open Finset

theorem inequalities_241693 (n : ℤ) :
    (∑ i ∈ range 21, (n + i) > 2019) ↔ n ≥ 87 := by 
  constructor
  · -- Forward direction: Assume the inequality holds, we need to derive n >= 87
    intro h
    norm_num [sum_range_succ] at h 
    omega 
  · -- Backward direction: Assume n >= 87, we need to derive the inequality
    intro h 
    norm_num [sum_range_succ] 
    omega