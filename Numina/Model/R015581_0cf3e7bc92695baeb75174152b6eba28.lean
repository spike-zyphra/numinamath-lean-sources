import Mathlib

theorem algebra_147728 (a : Fin 5 → ℕ) (ha : ∀ i j, i < j → a i < a j)
    (h : a 4 = 3 * a 0) (h' : ∑ i, a i = 31) :
    a 3 = 8 := by
  have h1 : a 0 < a 1 := by
    apply ha 0 1
    simp
  have h2 : a 1 < a 2 := by
    apply ha 1 2
    simp
  have h3 : a 2 < a 3 := by
    apply ha 2 3
    simp
  have h4 : a 3 < a 4 := by
    apply ha 3 4
    simp
  have h5 : a 0 + a 1 + a 2 + a 3 + a 4 = 31 := by 
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h'
    linarith 
  rw [h] at h5
  have h9 : a 3 < 3 * a 0 := by 
    linarith [h4, h]
  omega