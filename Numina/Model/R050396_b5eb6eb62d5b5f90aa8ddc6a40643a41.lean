import Mathlib

theorem algebra_93289 (a : ℕ → ℝ) (ha : a 0 = 1)
    (h : ∀ n ≥ 2, ∏ i ∈ Finset.range n, a i = n ^ 2) :
    a 2 + a 4 = 61 / 16 := by
  have ha1 : a 1 = 4 := by 
    have h2 := h 2 (by norm_num)
    simp [Finset.prod_range_succ, ha] at h2 
    nlinarith 
  have ha2 : a 2 = 9 / 4 := by 
    have h3 := h 3 (by norm_num)
    have h2 := h 2 (by norm_num)
    simp [Finset.prod_range_succ, ha, ha1] at h3 h2 
    nlinarith 
  have ha3 : a 3 = 16 / 9 := by 
    have h4 := h 4 (by norm_num)
    have h3 := h 3 (by norm_num)
    simp [Finset.prod_range_succ, ha, ha1, ha2] at h4 h3 
    nlinarith 
  have ha4 : a 4 = 25 / 16 := by 
    have h5 := h 5 (by norm_num)
    have h4 := h 4 (by norm_num)
    simp [Finset.prod_range_succ, ha, ha1, ha2, ha3] at h5 h4 
    nlinarith 
  rw [ha2, ha4]
  norm_num