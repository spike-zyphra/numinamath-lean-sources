import Mathlib

theorem algebra_13471 (x : Fin 4 → ℝ)
    (hx : x 0 = 100 ∧ x 1 = 200 ∧ x 2 = 150 ∧ x 3 = 150) :
    (∑ i, x i) / 4 = 150 := by
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
  rcases hx with ⟨hx0, hx1, hx2, hx3⟩
  norm_num [hx0, hx1, hx2, hx3]
  <;> try { linarith }