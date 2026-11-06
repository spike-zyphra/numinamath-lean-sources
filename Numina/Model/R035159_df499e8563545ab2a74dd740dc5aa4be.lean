import Mathlib

theorem algebra_114788 (x y : ℤ) :
    3 * x * y + y = 7 * x + 3 ↔ (x = 0 ∧ y = 3) ∨ (x = -1 ∧ y = 2) := by 
  constructor
  · -- Assume 3 * x * y + y = 7 * x + 3, prove (x = 0 ∧ y = 3) ∨ (x = -1 ∧ y = 2)
    rintro h 
    have h1 : y * (3 * x + 1) = 7 * x + 3 := by 
      linarith
    -- now from the eqation above, we can derive that 3x + 1 divides 2
    have h2 : (3 * x + 1) ∣ 2 := by 
      use 3 * y - 7
      nlinarith
    have h3 : (3 * x + 1) = 1 ∨ (3 * x + 1) = 2 ∨ (3 * x + 1) = -1 ∨ (3 * x + 1) = -2 := by 
      have h1 : (3 * x + 1) ∣ 2 := h2 
      have h2 : (3 * x + 1) ≤ 2 := by 
        apply Int.le_of_dvd (by norm_num) h1 
      have h3 : (3 * x + 1) ≥ -2 := by 
        have h4 : -(3 * x + 1) ∣ 2 := by 
          exact Int.neg_dvd.2 h1 
        have h5 : -(3 * x + 1) ≤ 2 := by 
          apply Int.le_of_dvd (by norm_num) h4 
        omega 
      interval_cases (3 * x + 1) <;> tauto 
    rcases h3 with h_eq | h_eq | h_eq | h_eq
    · -- 3 * x + 1 = 1 
      have hx0 : x = 0 := by 
        linarith 
      have hy3 : y = 3 := by 
        rw [hx0] at h1 
        nlinarith 
      left 
      exact ⟨hx0, hy3⟩ 
    · -- 3 * x + 1 = 2 
      exfalso 
      omega 
    · -- 3 * x + 1 = -1 
      exfalso 
      omega 
    · -- 3 * x + 1 = -2 
      have hx1 : x = -1 := by 
        linarith 
      have hy2 : y = 2 := by 
        rw [hx1] at h1 
        nlinarith 
      right 
      exact ⟨hx1, hy2⟩ 
  · -- Assume (x = 0 ∧ y = 3) ∨ (x = -1 ∧ y = 2), prove 3 * x * y + y = 7 * x + 3 
    rintro (h | h)
    · -- x = 0 ∧ y = 3 
      rcases h with ⟨hx, hy⟩ 
      rw [hx, hy] 
      all_goals norm_num 
    · -- x = -1 ∧ y = 2 
      rcases h with ⟨hx, hy⟩ 
      rw [hx, hy] 
      all_goals norm_num