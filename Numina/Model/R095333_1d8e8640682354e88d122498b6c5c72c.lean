import Mathlib

theorem algebra_232824 (a : Fin 5 → ℕ) (ha : ∀ i j, i < j → a i < a j)
    (h : ∑ i, a i = 27) (h' : a 4 = 3 * a 0) :
    a 2 = 5 := by 
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h
  have h1 : a 0 < a 1 := ha 0 1 (by simp)
  have h2 : a 1 < a 2 := ha 1 2 (by simp)
  have h3 : a 2 < a 3 := ha 2 3 (by simp)
  have h4 : a 3 < a 4 := ha 3 4 (by simp)
  -- The omega tactic will solve constraints over integers.
  omega