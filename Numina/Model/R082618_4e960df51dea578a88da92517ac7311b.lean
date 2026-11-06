import Mathlib

theorem number_theory_221815 (a : Fin 10 → ℕ) (ha : a = ![7, 1, 8, 4, 10, 6, 9, 3, 2, 5]) :
    ∀ i, a i ∣ ∑ j in Finset.univ.filter (· < i), a j := by 
  intro i
  rw [ha]
  fin_cases i <;> simp [Finset.sum_filter, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at *
  <;> try { native_decide }
  <;> try { norm_num }
  <;> try { tauto }