import Mathlib

theorem algebra_233928 (x y : ℤ) :
    x^2 - x * y - 2 * y^2 = 7 ↔ (x = 3 ∧ y = -2) ∨ (x = 5 ∧ y = 2) ∨
    (x = -3 ∧ y = 2) ∨ (x = -5 ∧ y = -2) := by 
  constructor
  · -- Forward implication: if x^2 - x*y - 2*y^2 = 7, prove the disjunction of the four solutions
    intro h
    have h1 : (x - 2 * y) * (x + y) = 7 := by
      ring_nf at h ⊢
      linarith
    have h2 : (x - 2 * y) ∣ 7 := by 
      use (x + y)
      linarith
    have h3 : (x - 2 * y) = 1 ∨ (x - 2 * y) = 7 ∨ (x - 2 * y) = -1 ∨ (x - 2 * y) = -7 := by
      have h4 : (x - 2 * y) ∣ 7 := by
        use (x + y)
        linarith
      have h5 : (x - 2 * y) ≤ 7 := by 
        apply Int.le_of_dvd (by norm_num)
        exact h4
      have h6 : (x - 2 * y) ≥ -7 := by 
        have h7 : (- (x - 2 * y)) ∣ 7 := by 
          exact Int.neg_dvd.mpr h4 
        have h8 : (- (x - 2 * y)) ≤ 7 := by 
          apply Int.le_of_dvd (by norm_num)
          exact h7
        linarith 
      interval_cases h8 : (x - 2 * y) <;> omega 
    rcases h3 with (h4 | h4 | h4 | h4)
    · 
      have h5 : x + y = 7 := by 
        rw [h4] at h1
        linarith
      have h6 : y = 2 := by 
        linarith
      have h7 : x = 5 := by 
        linarith
      simp [h7, h6]
    · 
      have h5 : x + y = 1 := by 
        rw [h4] at h1
        linarith
      have h6 : y = -2 := by 
        linarith
      have h7 : x = 3 := by 
        linarith
      simp [h7, h6]
    · 
      have h5 : x + y = -7 := by 
        rw [h4] at h1
        linarith
      have h6 : y = -2 := by 
        linarith
      have h7 : x = -5 := by 
        linarith
      simp [h7, h6]
    · 
      have h5 : x + y = -1 := by 
        rw [h4] at h1
        linarith
      have h6 : y = 2 := by 
        linarith
      have h7 : x = -3 := by 
        linarith
      simp [h7, h6]
  · -- Backward direction: check each of the four solutions 
    rintro (h | h | h | h)
    · 
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num 
    · 
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num 
    · 
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num 
    · 
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num