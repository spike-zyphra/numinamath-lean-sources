import Mathlib

theorem algebra_302883 {x y : ℕ} (hx : 9 * x + 6 * y ≤ 273) (hy : 12 * x + 3 * y ≤ 243)
    (h : x ≥ 0 ∧ y ≥ 0) :
    144 * x + 81 * y ≤ 3978 := by
  have h1 : x ≤ 30 := by
    omega
  have h2 : y ≤ 81 := by 
    omega 
  have h4 : y ≤ 45 := by
    by_contra h
    push_neg at h
    have h5 : y ≥ 46 := by omega 
    have h6 : 6 * y ≥ 276 := by 
      omega 
    have h7 : 9 * x + 6 * y ≥ 276 := by
      omega 
    omega 
  interval_cases x <;> interval_cases y 
    <;> omega