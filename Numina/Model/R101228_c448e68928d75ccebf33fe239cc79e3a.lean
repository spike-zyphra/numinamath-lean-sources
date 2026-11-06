import Mathlib

theorem inequalities_130147 (a : Fin 10 → ℝ) (h₀ : ∀ i j, i < j → a i ≤ a j) :
    (∑ i in Finset.range 6, a i) / 6 ≤ (∑ i in Finset.range 10, a i) / 10 := by 
  norm_num [Finset.sum_range_succ] at *
  <;> linarith [h₀ 0 1 (by simp), h₀ 1 2 (by simp), h₀ 2 3 (by simp), h₀ 3 4 (by simp), h₀ 4 5 (by simp), h₀ 5 6 (by simp), h₀ 6 7 (by simp), h₀ 7 8 (by simp), h₀ 8 9 (by simp)]