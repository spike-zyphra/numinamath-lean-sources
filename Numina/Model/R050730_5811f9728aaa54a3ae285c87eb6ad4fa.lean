import Mathlib

theorem algebra_271162 (x y : ℤ) : x * y = 20 - 3 * x + y ↔
    (x, y) = (2, 14) ∨ (x, y) = (18, -2) ∨ (x, y) = (0, -20) ∨ (x, y) = (-16, -4) := by
  constructor
  · -- Assume x * y = 20 - 3 * x + y, prove the disjunction of the four equalities
    rintro h_eq
    have h1 : x * y + 3 * x - y = 20 := by linarith

    have h2 : x * (y + 3) = y + 20 := by
      nlinarith

    have h4 : (y + 3) * (x - 1) = 17 := by 
      nlinarith
  
    have h6 : (y + 3) = 1 ∨ (y + 3) = -1 ∨ (y + 3) = 17 ∨ (y + 3) = -17 := by 
      have h7 : (y + 3) ∣ 17 := by 
        use (x - 1)
        nlinarith 
      have h8 : (y + 3) = 1 ∨ (y + 3) = -1 ∨ (y + 3) = 17 ∨ (y + 3) = -17 := by
        have h9 : (y + 3) ≤ 17 := by 
          apply Int.le_of_dvd (by norm_num) h7
        have h10 : (y + 3) ≥ -17 := by 
          have h11 : (- (y + 3)) ∣ 17 := by 
            exact Int.neg_dvd.2 h7
          have h12 : (- (y + 3)) ≤ 17 := by 
            apply Int.le_of_dvd (by norm_num) h11
          have h13 : (y + 3) ≥ -17 := by
            linarith 
          exact h13
        interval_cases k : (y + 3) <;> omega
      exact h8
  
    rcases h6 with h | h | h | h
  
    · -- Case (y + 3) = 1 
      have h_y : y = -2 := by 
        linarith 
      have h_x : x = 18 := by 
        nlinarith 
      simp [Prod.ext_iff, h_x, h_y]
  
    · -- Case (y + 3) = -1 
      have h_y : y = -4 := by 
        linarith 
      have h_x : x = -16 := by 
        nlinarith 
      simp [Prod.ext_iff, h_x, h_y]
  
    · -- Case (y + 3) = 17 
      have h_y : y = 14 := by 
        linarith 
      have h_x : x = 2 := by 
        nlinarith 
      simp [Prod.ext_iff, h_x, h_y]
  
    · -- Case (y + 3) = -17 
      have h_y : y = -20 := by 
        linarith 
      have h_x : x = 0 := by 
        nlinarith 
      simp [Prod.ext_iff, h_x, h_y]
  
  · -- Assume (x, y) is one of the four equalities, prove x * y = 20 - 3 * x + y
    rintro (h | h | h | h)
    · -- Case (x, y) = (2, 14)
      simp [Prod.ext_iff] at h ⊢
      <;> norm_num [h.1, h.2] 
    · -- Case (x, y) = (18, -2)
      simp [Prod.ext_iff] at h ⊢
      <;> norm_num [h.1, h.2] 
    · -- Case (x, y) = (0, -20)
      simp [Prod.ext_iff] at h ⊢
      <;> norm_num [h.1, h.2] 
    · -- Case (x, y) = (-16, -4)
      simp [Prod.ext_iff] at h ⊢
      <;> norm_num [h.1, h.2]