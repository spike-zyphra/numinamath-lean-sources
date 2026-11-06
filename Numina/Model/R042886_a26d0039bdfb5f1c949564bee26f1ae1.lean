import Mathlib

theorem number_theory_232416 (x y : ℤ) : x^2 = y^2 + 2 * y + 13 ↔
    (x = 4 ∧ y = -3) ∨ (x = 4 ∧ y = 1) ∨ (x = -4 ∧ y = 1) ∨ (x = -4 ∧ y = -3) := by
  constructor
  · -- Assume x^2 = y^2 + 2 * y + 13, prove the disjunction of the four solutions.
    intro h
    have h1 : x^2 - (y + 1)^2 = 12 := by
      nlinarith
    -- Factor the difference of squares
    have h2 : (x - (y + 1)) * (x + (y + 1)) = 12 := by
      nlinarith [h1]
    -- Show that x - (y + 1) divides 12
    have h3 : x - (y + 1) ∣ 12 := by
      use x + (y + 1)
      all_goals linarith [h2]
    -- Establish the bounds for x - (y + 1)
    have h4 : x - (y + 1) ≤ 12 := by
      apply Int.le_of_dvd (by norm_num) h3
    -- Establish the lower bound
    have h5 : x - (y + 1) ≥ -12 := by
      have h6 : -(x - (y + 1)) ∣ 12 := by
        exact Int.neg_dvd.2 h3
      have h7 : -(x - (y + 1)) ≤ 12 := by
        apply Int.le_of_dvd (by norm_num) h6
      omega
    -- Now use interval_cases to check all possible values
    interval_cases h6 : x - (y + 1) <;> norm_num at h2 h6 ⊢
    <;> try { 
      omega
    } 
    <;> try { 
      have hx : x ≤ 7 := by nlinarith
      have hx2 : x ≥ -7 := by nlinarith
      interval_cases x <;> omega
    }
  · -- Assume the disjunction of the four solutions, prove x^2 = y^2 + 2 * y + 13
    rintro (h | h | h | h)
    · -- Case (x = 4 ∧ y = -3)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (x = 4 ∧ y = 1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (x = -4 ∧ y = 1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (x = -4 ∧ y = -3)
      rcases h with ⟨rfl, rfl⟩
      norm_num