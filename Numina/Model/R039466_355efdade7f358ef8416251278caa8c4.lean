import Mathlib

theorem algebra_274725 (M D : ℕ) (hM : M > D) (hM' : M > 1) (hD : D > 1)
    (hCD : M^2 - D^2 = 24) : M = 7 := by
  have h1 : M^2 = D^2 + 24 := by 
    omega 
  have h8 : M ≤ 24 := by 
    nlinarith [sq_nonneg (M - (D : ℤ)), sq_nonneg (M + (D : ℤ)), h1, hM, hD]
  have h9 : D ≤ 24 := by nlinarith [h1, hM, hD]
  interval_cases M <;> try { 
    have h9 : D ≤ 24 := by nlinarith 
    interval_cases D <;> omega 
  }