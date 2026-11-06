import Mathlib

theorem algebra_10552 {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hsum : x^2 + y^2 = 90) (hprod : x * y = 27) :
    x + y = 12 := by 
  have h1 : x ≤ 27 := by 
    by_cases hx' : x ≤ 27
    · exact hx'
    · -- not h, so x > 27
      have : x > 27 := by omega 
      have h1 : y < 1 := by 
        by_contra h 
        push_neg at h 
        have : x * y ≥ 28 := by 
          nlinarith 
        linarith 
      have h1 : y ≤ 0 := by omega 
      linarith 
  have h2 : y ≤ 27 := by 
    by_cases hy' : y ≤ 27 
    · exact hy' 
    · -- not h, so y > 27 
      have : y > 27 := by omega 
      have h1 : x < 1 := by 
        by_contra h 
        push_neg at h 
        have : x * y ≥ 28 := by 
          nlinarith 
        linarith 
      have h1 : x ≤ 0 := by omega 
      linarith 
  interval_cases x <;> interval_cases y 
    <;> omega