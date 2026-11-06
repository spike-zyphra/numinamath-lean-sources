import Mathlib

theorem algebra_18916 (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (h : ∀ n ≥ 2, a n = ∑ i in Finset.Icc 1 (n - 1), a i) (ha19 : a 19 = 99) :
    a 20 = 198 := by
  have eq1 : a 20 = 2 * a 19 := by
    have h20 : a 20 = ∑ i in Finset.Icc 1 19, a i := by 
      specialize h 20 (by norm_num)
      simpa using h
    have h19 : a 19 = ∑ i in Finset.Icc 1 18, a i := by 
      specialize h 19 (by norm_num)
      simpa using h 
    have eq2 : ∑ i in Finset.Icc 1 19, a i = (∑ i in Finset.Icc 1 18, a i) + a 19 := by
      rw [Finset.sum_Icc_succ_top (by norm_num)]
    rw [h20]
    rw [eq2]
    have eq3 : (∑ i in Finset.Icc 1 18, a i) = a 19 := by 
      linarith [h19]
    rw [eq3]
    all_goals linarith 
  linarith [eq1, ha19]