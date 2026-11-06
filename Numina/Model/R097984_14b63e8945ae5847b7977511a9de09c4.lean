import Mathlib

theorem algebra_301980 (x : Fin 7 → ℕ) (hx : StrictMono x)
    (hxs : ∑ i, x i = 159) :
    x 0 + x 1 + x 2 ≤ 61 := by
  have g1 : x 0 < x 1 := hx (by simp)
  have g2 : x 1 < x 2 := hx (by simp)
  have g3 : x 2 < x 3 := hx (by simp)
  have g4 : x 3 < x 4 := hx (by simp)
  have g5 : x 4 < x 5 := hx (by simp)
  have g6 : x 5 < x 6 := hx (by simp)
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hxs
  omega