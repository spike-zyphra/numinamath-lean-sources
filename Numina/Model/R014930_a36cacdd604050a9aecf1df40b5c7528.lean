import Mathlib

open Real
open scoped BigOperators

theorem other_148820 :
  ∃ s : Finset ℝ, s.card = 3 ∧
  (∀ x ∈ s, x > 0) ∧
  (∑ x in s, x) / 3 = 1 := by 
  use {0.5, 1.0, 1.5}
  constructor 
  · -- Show that the cardinality is 3
    norm_num [Finset.card_insert_of_not_mem, Finset.card_singleton]
  constructor 
  · -- Show all elements are positive
    intro x hx 
    norm_num [Finset.mem_insert, Finset.mem_singleton] at hx ⊢ 
    rcases hx with (rfl | rfl | rfl) 
    all_goals norm_num 
  · -- Show the arithmetic mean is 1 
    norm_num [Finset.sum_insert, Finset.sum_singleton]