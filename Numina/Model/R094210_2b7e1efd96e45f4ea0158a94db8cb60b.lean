import Mathlib

open Real
open scoped BigOperators

theorem algebra_12616 {n : ℕ} {h : n ≥ 3} (hn : n * (n - 3) / 2 = 9) :
    n = 6 := by 
  have h1 : n ≤ 6 := by 
    by_contra h1
    push_neg at h1
    have h2 : n ≥ 7 := by 
      omega 
    have h3 : n * (n - 3) / 2 > 9 := by 
      have h4 : n ≥ 7 := h2 
      have h5 : n - 3 ≥ 4 := by 
        omega 
      have h6 : n * (n - 3) ≥ 28 := by 
        nlinarith [h4, h5] 
      have h7 : n * (n - 3) / 2 ≥ 14 := by 
        omega 
      linarith 
    linarith [hn, h3] 
  interval_cases n <;> omega