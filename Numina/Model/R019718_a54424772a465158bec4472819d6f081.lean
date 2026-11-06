import Mathlib

theorem algebra_138576 (R : Fin 6 → ℝ) (hR : ∀ i, R i = (i + 1)) (hR' : ∑ i, R i = 12) :
    (1 / (1 + 2 + 3 + 4 + 5 + 6)) * 12 = 4.32 := by
  have h1 : ∑ i : Fin 6, R i = 21 := by 
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, hR]
    all_goals norm_num
  linarith