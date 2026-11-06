import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_179291 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
  (hx : ∀ i, |x i| < 1)
  (hsum : ∑ i, |x i| = 19 + |∑ i, x i|) :
  n ≥ 20 := by
    by_contra h
    push_neg at h
    have h1 : n ≤ 19 := by omega

    have h2 : ∑ i, |x i| < 19 := by
      have h3 : n ≤ 19 := h1
      have h4 : ∀ i, |x i| < 1 := hx
      interval_cases n <;> simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] <;> 
        norm_num <;> 
        try { linarith [h4 0, h4 1, h4 2, h4 3, h4 4, h4 5, h4 6, h4 7, h4 8, h4 9, h4 10, h4 11, h4 12, h4 13, h4 14, h4 15, h4 16, h4 17, h4 18, h4 19] }
    
    have h3 : ∑ i, |x i| ≥ 19 := by
      have h4 : ∑ i, |x i| = 19 + |∑ i, x i| := hsum
      have h5 : |∑ i, x i| ≥ 0 := by 
        apply abs_nonneg
      linarith
    
    linarith [h2, h3]