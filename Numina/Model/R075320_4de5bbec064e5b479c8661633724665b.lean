import Mathlib

theorem inequalities_184292 (a : Fin 10 → ℝ) (h : ∀ i j, i < j → a i ≤ a j) :
    (1 / 6) * (∑ i in Finset.range 6, a i) ≤ (1 / 10) * (∑ i in Finset.range 10, a i) := by 
  simp [Finset.sum_range_succ] at *
  norm_num at *
  linarith [h 0 1 (by decide), h 1 2 (by decide), h 2 3 (by decide), h 3 4 (by decide), h 4 5 (by decide),
    h 5 6 (by decide), h 6 7 (by decide), h 7 8 (by decide), h 8 9 (by decide)]