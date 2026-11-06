import Mathlib

theorem algebra_185034 {f : ℝ → ℝ} (hf : f = fun x => 3 * x ^ 5 - 250 * x ^ 3 + 735 * x) :
    ∃ s : Finset ℝ, s.card = 5 ∧ ∑ x ∈ s, x = 75 := by
  use {0, 5, 10, 15, 45}
  constructor
  · -- Show that the cardinality is 5
    norm_num [Finset.card_insert_of_not_mem, Finset.card_singleton]
    all_goals norm_num
  · -- Show that the sum is 75
    norm_num [Finset.sum_insert, Finset.sum_singleton]
    all_goals norm_num