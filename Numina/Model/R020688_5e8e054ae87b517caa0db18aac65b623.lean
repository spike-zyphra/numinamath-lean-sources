import Mathlib

theorem algebra_5091 : IsLeast {z : ℤ | ∃ x y, x - x * y - y = 9 ∧ z = x * y} (-22) := by
  constructor
  · -- Show that -22 is in the set
    use -2, 11
    all_goals norm_num
  · -- Show that -22 is the minimum
    intro z h
    rcases h with ⟨x, y, h_eq, hz⟩
    have h_eq1 : x - x * y - y = 9 := h_eq
    have h_eq2 : (x + 1) * (1 - y) = 10 := by
      nlinarith
    have h1 : (x + 1) * (1 - y) = 10 := h_eq2
    have h2 : (x + 1) ∣ 10 := by
      use (1 - y)
      all_goals linarith
    have h3 : (x + 1) = 1 ∨ (x + 1) = -1 ∨ (x + 1) = 2 ∨ (x + 1) = -2 ∨ (x + 1) = 5 ∨ (x + 1) = -5 ∨ (x + 1) = 10 ∨ (x + 1) = -10 := by
      have h2' : (x + 1) ∣ 10 := h2
      have h4 : (x + 1) ≤ 10 := by 
        apply Int.le_of_dvd (by norm_num) h2'
      have h5 : (x + 1) ≥ -10 := by
        have h6 : (- (x + 1)) ∣ 10 := by
          exact Int.neg_dvd.2 h2'
        have h7 : - (x + 1) ≤ 10 := by
          apply Int.le_of_dvd (by norm_num) h6
        omega
      interval_cases (x + 1) <;> tauto 
    rcases h3 with (h_eq3 | h_eq3 | h_eq3 | h_eq3 | h_eq3 | h_eq3 | h_eq3 | h_eq3)
    · -- Case x + 1 = 1 => x = 0 
      have h1 : x = 0 := by linarith 
      have h2 : y = -9 := by 
        rw [h1] at h_eq2
        linarith
      have h4 : z = 0 := by 
        rw [show z = x * y by linarith [hz], h1, h2]
        all_goals norm_num 
      linarith 
    · -- Case x + 1 = -1 => x = -2
      have h1 : x = -2 := by linarith 
      have h2 : y = 11 := by 
        rw [h1] at h_eq2
        linarith
      have h4 : z = -22 := by 
        rw [show z = x * y by linarith [hz], h1, h2]
        all_goals norm_num 
      linarith 
    · -- Case x + 1 = 2 => x = 1 
      have h1 : x = 1 := by linarith 
      have h2 : y = -4 := by 
        rw [h1] at h_eq2
        linarith 
      have h4 : z = -4 := by 
        rw [show z = x * y by linarith [hz], h1, h2]
        all_goals norm_num 
      linarith 
    · -- Case x + 1 = -2 => x = -3
      have h1 : x = -3 := by linarith 
      have h2 : y = 6 := by 
        rw [h1] at h_eq2
        linarith
      have h4 : z = -18 := by 
        rw [show z = x * y by linarith [hz], h1, h2]
        all_goals norm_num 
      linarith 
    · -- Case x + 1 = 5 => x = 4
      have h1 : x = 4 := by linarith 
      have h2 : y = -1 := by 
        rw [h1] at h_eq2
        linarith 
      have h4 : z = -4 := by 
        rw [show z = x * y by linarith [hz], h1, h2]
        all_goals norm_num 
      linarith 
    · -- Case x + 1 = -5 => x = -6
      have h1 : x = -6 := by linarith 
      have h2 : y = 3 := by 
        rw [h1] at h_eq2
        linarith 
      have h4 : z = -18 := by 
        rw [show z = x * y by linarith [hz], h1, h2]
        all_goals norm_num 
      linarith 
    · -- Case x + 1 = 10 => x = 9 
      have h1 : x = 9 := by linarith 
      have h2 : y = 0 := by 
        rw [h1] at h_eq2
        linarith 
      have h4 : z = 0 := by 
        rw [show z = x * y by linarith [hz], h1, h2]
        all_goals norm_num 
      linarith 
    · -- Case x + 1 = -10 => x = -11
      have h1 : x = -11 := by linarith 
      have h2 : y = 2 := by 
        rw [h1] at h_eq2
        linarith
      have h4 : z = -22 := by 
        rw [show z = x * y by linarith [hz], h1, h2]
        all_goals norm_num 
      linarith