import Mathlib

theorem number_theory_250772 (a : Fin 7 → ℕ) (ha : a 0 = 1234567 ∧ a 1 = 2345671 ∧ a 2 = 3456712 ∧ a 3 = 4567123 ∧ a 4 = 5671234 ∧ a 5 = 6712345 ∧ a 6 = 7123456) :
    (∑ i, a i) / 7 = 4444444 := by 
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6⟩
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, ha0, ha1, ha2, ha3, ha4, ha5, ha6]
  all_goals norm_num