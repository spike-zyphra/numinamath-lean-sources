import Mathlib

theorem other_137360 (t : Fin 7 → ℝ)
    (ht : t 0 = 1 ∧ t 1 = 0.5 ∧ t 2 = 1 ∧ t 3 = 0.5 ∧ t 4 = 0.5 ∧ t 5 = 0.5 ∧ t 6 = 2) :
    ∑ i, t i ≥ 5 := by
  rcases ht with ⟨ht0, ht1, ht2, ht3, ht4, ht5, ht6⟩
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, ht0, ht1, ht2, ht3, ht4, ht5, ht6]
  all_goals norm_num