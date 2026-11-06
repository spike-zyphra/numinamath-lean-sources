import Mathlib

theorem algebra_113354 (x : Fin 102 → ℝ) (hx : ∀ i, x i = i / 101) :
    ∑ i, (x i)^3 / (1 - 3 * x i + 3 * (x i)^2) = 51 := by
  simp_all [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, hx]
  norm_num