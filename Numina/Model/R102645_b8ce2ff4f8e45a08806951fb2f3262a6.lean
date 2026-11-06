import Mathlib

theorem algebra_1371 (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (h : x + y + x * y = 34) :
    (x = 4 ∧ y = 6) ∨ (x = 6 ∧ y = 4) := by
  have h1 : (x + 1) * (y + 1) = 35 := by
    nlinarith 
  have h2 : x ≤ 17 := by 
    have h4 : y + 1 > 0 := by nlinarith 
    have h5 : (x + 1) > 0 := by nlinarith 
    have h6 : (x + 1) * (y + 1) = 35 := h1 
    have h7 : (x + 1) ≤ 35 := by 
      have h8 : (x + 1) ∣ 35 := by 
        use (y + 1)
        all_goals nlinarith 
      have h9 : (x + 1) ∣ 35 := h8 
      have h10 : (x + 1) ≤ 35 := by 
        apply Int.le_of_dvd (by norm_num) h9 
      linarith 
    have h9 : (x + 1) ≤ 35 := h7 
    nlinarith 
  have h3 : y ≤ 17 := by 
    have h4 : x + 1 > 0 := by nlinarith 
    have h5 : (y + 1) > 0 := by nlinarith 
    have h6 : (x + 1) * (y + 1) = 35 := h1 
    have h7 : (y + 1) ≤ 35 := by 
      have h8 : (y + 1) ∣ 35 := by 
        use (x + 1)
        all_goals nlinarith 
      have h9 : (y + 1) ∣ 35 := h8 
      have h10 : (y + 1) ≤ 35 := by 
        apply Int.le_of_dvd (by norm_num) h9 
      linarith 
    have h9 : (y + 1) ≤ 35 := h7 
    nlinarith 
  interval_cases x <;> interval_cases y 
    <;> omega