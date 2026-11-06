import Mathlib

theorem algebra_19979 (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : 3 * x + 2 * y + x * y = 115) : x + y = 17 := by
  have h_eq : (x + 2) * (y + 3) = 121 := by
    nlinarith
  have h1 : x ≤ 119 := by
    have h2 : (x + 2) * (y + 3) = 121 := h_eq
    have h3 : x + 2 ≤ 121 := by 
      have h4 : y + 3 > 0 := by 
        omega
      nlinarith 
    omega 
  have h2 : y ≤ 119 := by 
    have h2 : (x + 2) * (y + 3) = 121 := h_eq 
    have h3 : y + 3 ≤ 121 := by 
      have h4 : x + 2 > 0 := by 
        omega
      nlinarith 
    omega 
  interval_cases x <;> omega