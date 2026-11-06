import Mathlib

theorem algebra_19758 {n : ℕ} (hn : n % 6 = 0) (h : n / 6 + 5 ≥ 20) :
    n ≥ 90 := by 
  have h1 : n / 6 ≥ 15 := by
    omega 
  have h5 : n / 6 * 6 ≥ 15 * 6 := by 
    have h6 : n / 6 ≥ 15 := h1 
    nlinarith 
  have h4 : n / 6 * 6 ≤ n := by 
    have h5' : n % 6 = 0 := hn 
    have h8 : n = (n / 6) * 6 := by
      omega 
    nlinarith [h8]
  omega