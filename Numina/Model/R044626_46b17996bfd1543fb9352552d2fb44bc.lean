import Mathlib

theorem algebra_20691 (a : Fin 5 → ℝ) (ha : a 0 = 6 ∧ a 1 = 8 ∧ a 2 = 9 ∧ a 3 = 11 ∧ a 4 = 16) :
    (∑ i : Fin 5, a i) / 5 = 10 := by
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, ha0, ha1, ha2, ha3, ha4]
  all_goals norm_num