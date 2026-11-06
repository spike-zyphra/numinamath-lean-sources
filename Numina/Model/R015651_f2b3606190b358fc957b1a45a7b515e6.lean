import Mathlib

theorem algebra_192825 (x y : ℕ) (hx : x > 0) (hy : y > 0)
    (h : x^3 + 3 * x^2 * y + 8 * x * y^2 + 6 * y^3 = 87) :
    x + 2 * y = 5 := by
  have h1 : (x + y) * (x^2 + 2 * x * y + 6 * y^2) = 87 := by
    nlinarith [h]
  have h2 : x + y ∣ 87 := by 
    use x^2 + 2 * x * y + 6 * y^2 
    all_goals nlinarith [h1]
  have h3 : x ^ 2 + 2 * x * y + 6 * y ^ 2 ∣ 87 := by 
    use x + y 
    all_goals nlinarith [h1]
  have h4 : x + y ≤ 87 := by 
    have h5 : (x + y) ∣ 87 := h2
    have h6 : (x + y) ≤ 87 := by 
      exact Nat.le_of_dvd (by norm_num) h5 
    linarith 
  have h5 : x ^ 2 + 2 * x * y + 6 * y ^ 2 ≤ 87 := by 
    have h6 : (x ^ 2 + 2 * x * y + 6 * y ^ 2) ∣ 87 := h3 
    have h7 : (x ^ 2 + 2 * x * y + 6 * y ^ 2) ≤ 87 := by
      exact Nat.le_of_dvd (by norm_num) h6 
    linarith 
  have h6 : x + y = 3 := by
    have h7 : (x + y) ∣ 87 := h2
    have h8 : (x ^ 2 + 2 * x * y + 6 * y ^ 2) ∣ 87 := h3
    have h9 : (x + y) ≤ 87 := by 
      exact Nat.le_of_dvd (by norm_num) h7
    interval_cases h10 : x + y <;> 
      try { 
        omega 
      }
      <;> try { 
        norm_num at h1 h7 h8 
        all_goals 
          have : x ≤ 30 := by nlinarith 
          have : y ≤ 30 := by nlinarith 
          interval_cases x <;> omega 
      }
  -- Now we can solve for x and y.
  have h7 : y = 2 := by
    have h8 : x + y = 3 := h6 
    have : x ≤ 3 := by omega
    interval_cases x <;> omega 
  -- From y = 2 and x + y = 3, solve for x.
  have h8 : x = 1 := by 
    omega 
  -- Now we can complete the proof.
  omega