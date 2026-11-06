import Mathlib

open Real

theorem algebra_142246 (X : Fin 6 → ℝ) (hX : ∀ i, X i = i + 1)
    (pX : Fin 6 → ℝ) (hpX : ∀ i, pX i = if i = 0 then 0.05 else (if i = 1 then 0.10 else (if i = 2 then 0.25 else (if i = 3 then 0.30 else (if i = 4 then 0.20 else (if i = 5 then 0.10 else 0)))))) :
    ∑ i, (if |X i - (∑ j, X j * pX j)| < 2 then pX i else 0) = 0.85 := by
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, hX, hpX]
  norm_num [abs_lt]
  <;> try { linarith }