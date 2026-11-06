import Mathlib

theorem number_theory_15497 (S : Finset ℕ) (hS : S = {23, 29}) :
    (S.sum id) / S.card = 26 := by
  rw [hS]
  norm_num [Finset.sum_insert, Finset.sum_singleton]