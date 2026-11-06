import Mathlib

theorem inequalities_602460 (a : Fin 10 → ℝ) (h : ∀ i j, i < j → a i ≤ a j) :
    (∑ i in Finset.range 6, a i) / 6 ≤ (∑ i in Finset.range 10, a i) / 10 := by 
  have h1 : (∑ i in Finset.range 6, a i) / 6 ≤ (∑ i in Finset.range 10, a i) / 10 := by 
    norm_num [Finset.sum_range_succ] at *
    all_goals 
      linarith [h 0 1 (by simp), h 0 2 (by simp), h 0 3 (by simp), h 0 4 (by simp), h 0 5 (by simp), h 0 6 (by simp), h 0 7 (by simp), h 0 8 (by simp), h 0 9 (by simp), h 1 2 (by simp), h 1 3 (by simp), h 1 4 (by simp), h 1 5 (by simp), h 1 6 (by simp), h 1 7 (by simp), h 1 8 (by simp), h 1 9 (by simp), h 2 3 (by simp), h 2 4 (by simp), h 2 5 (by simp), h 2 6 (by simp), h 2 7 (by simp), h 2 8 (by simp), h 2 9 (by simp), h 3 4 (by simp), h 3 5 (by simp), h 3 6 (by simp), h 3 7 (by simp), h 3 8 (by simp), h 3 9 (by simp), h 4 5 (by simp), h 4 6 (by simp), h 4 7 (by simp), h 4 8 (by simp), h 4 9 (by simp), h 5 6 (by simp), h 5 7 (by simp), h 5 8 (by simp), h 5 9 (by simp), h 6 7 (by simp), h 6 8 (by simp), h 6 9 (by simp), h 7 8 (by simp), h 7 9 (by simp), h 8 9 (by simp)]
  linarith