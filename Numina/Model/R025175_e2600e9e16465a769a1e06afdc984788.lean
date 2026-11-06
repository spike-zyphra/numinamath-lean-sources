import Mathlib

theorem algebra_187083 : ((2 + Real.sqrt 3)^4 + (2 - Real.sqrt 3)^4) / ((2 + Real.sqrt 3)^6 + (2 - Real.sqrt 3)^6) = 97 / 1351 := by
  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ 3 by norm_num)
  have h2 : Real.sqrt 3 ^ 4 = 9 := by
    calc
      Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 := by ring
      _ = 3 ^ 2 := by rw [h1]
      _ = 9 := by norm_num

  have h3 : (2 + Real.sqrt 3)^2 = 7 + 4 * Real.sqrt 3 := by
    nlinarith [h1, Real.sqrt_nonneg 3]

  have h4 : (2 - Real.sqrt 3)^2 = 7 - 4 * Real.sqrt 3 := by
    nlinarith [h1, Real.sqrt_nonneg 3]

  have h5 : (2 + Real.sqrt 3)^4 = (7 + 4 * Real.sqrt 3) ^ 2 := by
    calc
      (2 + Real.sqrt 3)^4 = ((2 + Real.sqrt 3) ^ 2) ^ 2 := by ring
      _ = (7 + 4 * Real.sqrt 3) ^ 2 := by rw [h3]

  have h6 : (2 - Real.sqrt 3) ^4 = (7 - 4 * Real.sqrt 3) ^2 := by
    calc
      (2 - Real.sqrt 3) ^4 = ((2 - Real.sqrt 3) ^ 2) ^ 2 := by ring
      _ = (7 - 4 * Real.sqrt 3) ^ 2 := by rw [h4]

  have h7 : (2 + Real.sqrt 3)^4 + (2 - Real.sqrt 3)^4 = 194 := by
    rw [h5, h6]
    nlinarith [h1, Real.sqrt_nonneg 3]

  have h8 : (2 + Real.sqrt 3)^3 = 26 + 15 * Real.sqrt 3 := by
    calc
      (2 + Real.sqrt 3)^3 = (2 + Real.sqrt 3) * (2 + Real.sqrt 3) ^ 2 := by ring
      _ = (2 + Real.sqrt 3) * (7 + 4 * Real.sqrt 3) := by rw [h3]
      _ = 26 + 15 * Real.sqrt 3 := by 
        nlinarith [h1, Real.sqrt_nonneg 3]

  have h9 : (2 - Real.sqrt 3)^3 = 26 - 15 * Real.sqrt 3 := by
    calc
      (2 - Real.sqrt 3)^3 = (2 - Real.sqrt 3) * (2 - Real.sqrt 3) ^ 2 := by ring
      _ = (2 - Real.sqrt 3) * (7 - 4 * Real.sqrt 3) := by rw [h4]
      _ = 26 - 15 * Real.sqrt 3 := by 
        nlinarith [h1, Real.sqrt_nonneg 3]

  have h10 : (2 + Real.sqrt 3)^6 = (26 + 15 * Real.sqrt 3) ^ 2 := by 
    calc
      (2 + Real.sqrt 3)^6 = ((2 + Real.sqrt 3) ^ 3) ^ 2 := by ring
      _ = (26 + 15 * Real.sqrt 3) ^ 2 := by rw [h8]

  have h11 : (2 - Real.sqrt 3) ^6 = (26 - 15 * Real.sqrt 3) ^2 := by 
    calc
      (2 - Real.sqrt 3) ^6 = ((2 - Real.sqrt 3) ^ 3) ^ 2 := by ring
      _ = (26 - 15 * Real.sqrt 3) ^ 2 := by rw [h9]

  have h12 : (2 + Real.sqrt 3) ^6 + (2 - Real.sqrt 3) ^6 = 2702 := by 
    rw [h10, h11]
    nlinarith [h1, Real.sqrt_nonneg 3]

  rw [h7, h12]
  all_goals norm_num