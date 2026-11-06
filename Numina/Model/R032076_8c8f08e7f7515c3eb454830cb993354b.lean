import Mathlib

theorem algebra_4928 :
  IsLeast {z : ℤ | ∃ x y : ℤ, z = x * y ∧ 6 * x + 2 * x * y + y = 16} (-18) := by
  constructor
  · -- Show that -18 is indeed in the set
    use 9, -2
    all_goals norm_num
  · -- Show that -18 is the minimum
    intro z h
    rcases h with ⟨x, y, hz, h_eq⟩
    have h1 : (2 * x + 1) * (y + 3) = 19 := by
      linarith
    have h2 : (2 * x + 1) ∣ 19 := by
      use y + 3
      all_goals linarith
    have h3 : (2 * x + 1) = 1 ∨ (2 * x + 1) = -1 ∨ (2 * x + 1) = 19 ∨ (2 * x + 1) = -19 := by
      have h4 : (2 * x + 1) ∣ 19 := h2
      have h5 : (2 * x + 1) ≤ 19 := by
        apply Int.le_of_dvd (by norm_num) h4
      have h6 : (2 * x + 1) ≥ -19 := by
        have h7 : (- (2 * x + 1)) ∣ 19 := by
          exact Int.neg_dvd.2 h4
        have h8 : - (2 * x + 1) ≤ 19 := by
          apply Int.le_of_dvd (by norm_num) h7
        linarith
      interval_cases (2 * x + 1) <;> try { tauto }
    rcases h3 with h3 | h3 | h3 | h3
    · -- Case 2 * x + 1 = 1
      have eq1 : y + 3 = 19 := by
        rw [h3] at h1
        linarith
      have hx : x = 0 := by
        linarith
      have hy : y = 16 := by
        linarith
      rw [hz]
      rw [hx, hy]
      all_goals norm_num
    · -- Case 2 * x + 1 = -1
      have eq1 : y + 3 = -19 := by
        rw [h3] at h1
        linarith
      have hx : x = -1 := by
        linarith
      have hy : y = -22 := by
        linarith
      rw [hz]
      rw [hx, hy]
      all_goals norm_num
    · -- Case 2 * x + 1 = 19
      have eq1 : y + 3 = 1 := by
        rw [h3] at h1
        linarith
      have hx : x = 9 := by
        linarith
      have hy : y = -2 := by
        linarith
      rw [hz]
      rw [hx, hy]
      all_goals norm_num
    · -- Case 2 * x + 1 = -19
      have eq1 : y + 3 = -1 := by
        rw [h3] at h1
        linarith
      have hx : x = -10 := by
        linarith
      have hy : y = -4 := by
        linarith
      rw [hz]
      rw [hx, hy]
      all_goals norm_num