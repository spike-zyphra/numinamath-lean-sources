import Mathlib

theorem number_theory_201166 (a : Fin 100 → ℕ) (h : {x | ∃ i, x = a i ∧ Even x}.encard = 32) :
    {x | ∃ i, x = a i ∧ Even x}.encard ≤ 33 := by
  rw [h]
  norm_num
  all_goals try { rfl }
  all_goals try { norm_num }
  all_goals try { linarith }