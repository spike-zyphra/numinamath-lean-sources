import Mathlib

theorem algebra_177524 (x y : ℤ) :
    2*x^2-2*x*y-5*x-y+19=0 ↔ (x=-6 ∧ y=-11) ∨ (x=-1 ∧ y=-26) ∨ (x=0 ∧ y=19) ∨ (x=5 ∧ y=4) := by
  constructor
  · -- Assume we have the equation, prove the disjunction
    intro h
    have h1 : (2 * x + 1) * y = 2 * x ^ 2 - 5 * x + 19 := by
      linarith 
    have h2 : (2 * x + 1) ∣ 22 := by
      use y - (x - 3)
      nlinarith
    have h3 : (2 * x + 1) = 1 ∨ (2 * x + 1) = 2 ∨ (2 * x + 1) = 11 ∨ (2 * x + 1) = 22 ∨ (2 * x + 1) = -1 ∨ (2 * x + 1) = -2 ∨ (2 * x + 1) = -11 ∨ (2 * x + 1) = -22 := by 
      have h4 : (2 * x + 1) ∣ 22 := h2 
      have h5 : (2 * x + 1) ≤ 22 := by 
        apply Int.le_of_dvd (by norm_num) h4 
      have h6 : (2 * x + 1) ≥ -22 := by 
        have h7 : -(2 * x + 1) ∣ 22 := by 
          exact Int.neg_dvd.2 h4 
        have h8 : -(2 * x + 1) ≤ 22 := by 
          apply Int.le_of_dvd (by norm_num) h7 
        linarith 
      interval_cases h7 : (2 * x + 1) <;> tauto 
    rcases h3 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4)
    · -- case 2 * x + 1 = 1, so x = 0 
      have h5 : x = 0 := by 
        omega 
      have h6 : y = 19 := by 
        rw [h5] at h1 
        omega 
      simp [h5, h6]
    · -- case 2 * x + 1 = 2, no integer solution 
      exfalso 
      omega 
    · -- case 2 * x + 1 = 11, so x = 5 
      have h5 : x = 5 := by 
        omega 
      have h6 : y = 4 := by 
        rw [h5] at h1 
        omega 
      simp [h5, h6]
    · -- case 2 * x + 1 = 22, no integer solution 
      exfalso 
      omega 
    · -- case 2 * x + 1 = -1, so x = -1 
      have h5 : x = -1 := by 
        omega 
      have h6 : y = -26 := by 
        rw [h5] at h1 
        omega 
      simp [h5, h6]
    · -- case 2 * x + 1 = -2, no integer solution 
      exfalso 
      omega 
    · -- case 2 * x + 1 = -11, so x = -6 
      have h5 : x = -6 := by 
        omega 
      have h6 : y = -11 := by 
        rw [h5] at h1 
        omega 
      simp [h5, h6]
    · -- case 2 * x + 1 = -22, no integer solution 
      exfalso 
      omega 
  · -- Assume disjunction, prove equation 
    rintro (h | h | h | h)
    · -- First case (x=-6 ∧ y=-11)
      rcases h with ⟨h1, h2⟩ 
      rw [h1, h2]
      all_goals norm_num 
    · -- Second case (x=-1 ∧ y=-26)
      rcases h with ⟨h1, h2⟩ 
      rw [h1, h2]
      all_goals norm_num 
    · -- Third case (x=0 ∧ y=19)
      rcases h with ⟨h1, h2⟩ 
      rw [h1, h2]
      all_goals norm_num 
    · -- Fourth case (x=5 ∧ y=4)
      rcases h with ⟨h1, h2⟩ 
      rw [h1, h2]
      all_goals norm_num