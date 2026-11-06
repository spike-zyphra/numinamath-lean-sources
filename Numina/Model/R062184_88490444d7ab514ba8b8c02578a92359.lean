import Mathlib

theorem number_theory_111009 (x y : ℤ) :
    x^2 = 7 + y^2 ↔ (x = 4 ∧ y = 3) ∨ (x = 4 ∧ y = -3) ∨ (x = -4 ∧ y = -3) ∨ (x = -4 ∧ y = 3) := by 
  constructor
  · -- Assume x^2 = 7 + y^2, prove (x = 4 ∧ y = 3) ∨ (x = 4 ∧ y = -3) ∨ (x = -4 ∧ y = -3) ∨ (x = -4 ∧ y = 3)
    intro h
    have h1 : x^2 - y^2 = 7 := by linarith 
    have h2 : (x - y) * (x + y) = 7 := by 
      linarith [h1]
    have h3 : (x - y) ∣ 7 := by 
      use (x + y)
      linarith 
    have h4 : (x - y) ∣ 7 := h3 
    have h5 : (x - y) = 1 ∨ (x - y) = 7 ∨ (x - y) = -1 ∨ (x - y) = -7 := by 
      have h6 : (x - y) ∣ 7 := h4 
      have h7 : (x - y) ≤ 7 := by 
        exact Int.le_of_dvd (show 0 < 7 by norm_num) h6 
      have h8 : (x - y) ≥ -7 := by 
        have h9 : (- (x - y)) ∣ 7 := by 
          exact Int.neg_dvd.2 h6 
        have h10 : (- (x - y)) ≤ 7 := by 
          exact Int.le_of_dvd (show 0 < 7 by norm_num) h9 
        linarith 
      interval_cases (x - y) <;> tauto 
    rcases h5 with (h5 | h5 | h5 | h5)
    · 
      have h6 : (x + y) = 7 := by 
        nlinarith 
      have h7 : x = 4 := by 
        linarith [h5, h6] 
      have h8 : y = 3 := by 
        linarith [h7, h6] 
      left 
      exact ⟨h7, h8⟩ 
    · 
      have h6 : (x + y) = 1 := by 
        nlinarith 
      have h7 : x = 4 := by 
        linarith [h5, h6] 
      have h8 : y = -3 := by 
        linarith [h7, h6] 
      right 
      left 
      exact ⟨h7, h8⟩ 
    · 
      have h6 : (x + y) = -7 := by 
        nlinarith 
      have h7 : x = -4 := by 
        linarith [h5, h6] 
      have h8 : y = -3 := by 
        linarith [h7, h6] 
      right 
      right 
      left 
      exact ⟨h7, h8⟩ 
    · 
      have h6 : (x + y) = -1 := by 
        nlinarith 
      have h7 : x = -4 := by 
        linarith [h5, h6] 
      have h8 : y = 3 := by 
        linarith [h7, h6] 
      right 
      right 
      right 
      exact ⟨h7, h8⟩ 
  · -- Assume (x = 4 ∧ y = 3) ∨ (x = 4 ∧ y = -3) ∨ (x = -4 ∧ y = -3) ∨ (x = -4 ∧ y = 3), prove x^2 = 7 + y^2
    rintro (h | h | h | h)
    · -- Case (x = 4 ∧ y = 3)
      rcases h with ⟨hx, hy⟩ 
      rw [hx, hy] 
      norm_num 
    · -- Case (x = 4 ∧ y = -3)
      rcases h with ⟨hx, hy⟩ 
      rw [hx, hy] 
      norm_num 
    · -- Case (x = -4 ∧ y = -3)
      rcases h with ⟨hx, hy⟩ 
      rw [hx, hy] 
      norm_num 
    · -- Case (x = -4 ∧ y = 3)
      rcases h with ⟨hx, hy⟩ 
      rw [hx, hy] 
      norm_num