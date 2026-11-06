import Mathlib

theorem algebra_5005 :
  IsLeast {z : ℤ | ∃ x y, z = x * y ∧ 2 * x - x * y + y = 7} (-12) := by
  constructor
  · -- Show that -12 is in the set
    use -4, 3
    all_goals norm_num
  · -- Show that -12 is minimal in the set
    intro z h
    rcases h with ⟨x, y, h1, h2⟩
    have h3 : x - 1 ∣ 5 := by
      have eq1 : y * (x - 1) = 2 * x - 7 := by
        linarith
      have h5 : x - 1 ∣ 2 * x - 7 := by
        have h1 : x - 1 ∣ y * (x - 1) := by
          use y
          all_goals linarith
        have h2 : y * (x - 1) = 2 * x - 7 := by
          linarith [eq1]
        rw [h2] at h1
        exact h1
      have h4 : x - 1 ∣ 5 := by
        have h5 : x - 1 ∣ 2 * x - 7 := h5
        have h6 : x - 1 ∣ 2 * (x - 1) := by
          use 2
          all_goals ring
        have h7 : x - 1 ∣ (2 * x - 7 - 2 * (x - 1)) := by
          apply Dvd.dvd.sub 
          · exact h5
          · exact h6
        have h8 : (2 * x - 7 - 2 * (x - 1)) = -5 := by
          linarith
        rw [h8] at h7
        have h9 : x - 1 ∣ (-5 : ℤ) := h7
        have h10 : x - 1 ∣ (5 : ℤ) := by
          exact Int.dvd_neg.mp h9
        exact h10
      exact h4
    have h5 : x - 1 = -5 ∨ x - 1 = -1 ∨ x - 1 = 1 ∨ x - 1 = 5 := by
      have h4 : x - 1 ∣ 5 := h3
      have h5 : x - 1 ≤ 5 := by
        apply Int.le_of_dvd (by norm_num) h4
      have h6 : x - 1 ≥ -5 := by
        have h7 : (- (x - 1) ) ∣ 5 := by 
          exact Int.neg_dvd.2 h4
        have h8 : - (x - 1) ≤ 5 := by
          apply Int.le_of_dvd (by norm_num) h7
        omega
      interval_cases h : x - 1 <;> tauto
    rcases h5 with (h5 | h5 | h5 | h5)
    · -- Case x - 1 = -5, so x = -4
      have hx : x = -4 := by 
        omega
      have hy : y = 3 := by 
        rw [hx] at h2
        omega
      rw [h1, hx, hy]
      all_goals norm_num
    · -- Case x - 1 = -1, so x = 0
      have hx : x = 0 := by 
        omega
      have hy : y = 7 := by 
        rw [hx] at h2
        omega
      rw [h1, hx, hy]
      all_goals norm_num
    · -- Case x - 1 = 1, so x = 2
      have hx : x = 2 := by 
        omega
      have hy : y = -3 := by 
        rw [hx] at h2
        omega
      rw [h1, hx, hy]
      all_goals norm_num
    · -- Case x - 1 = 5, so x = 6
      have hx : x = 6 := by 
        omega
      have hy : y = 1 := by 
        rw [hx] at h2
        omega
      rw [h1, hx, hy]
      all_goals norm_num