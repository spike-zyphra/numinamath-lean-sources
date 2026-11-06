import Mathlib

theorem algebra_322271 :
    IsGreatest {z : ℤ | ∃ x y, z = x ^ 2 + y ^ 2 ∧ x * y + 2 = 2 * (x + y)} 25 := by
  constructor
  · -- Show that 25 is in the set, using x = 3 and y = 4.
    use 3, 4
    all_goals norm_num
  · -- Show that if z is in the set and z > 25, then that's impossible.
    intro z h
    rcases h with ⟨x, y, h1, h2⟩
    -- Substitute z with x^2 + y^2 in the inequality
    rw [h1] at *
    -- Derive the equation (x - 2)(y - 2) = 2.
    have h3 : (x - 2) * (y - 2) = 2 := by
      nlinarith
    -- Now, find all integer solutions to (x - 2)(y - 2) = 2.
    have h4 : (x - 2) * (y - 2) = 2 := h3
    have h5 : (x - 2) ∣ 2 := by
      use y - 2
      all_goals linarith
    -- There are only finitely many integers dividing 2.
    have h6 : (x - 2) = 1 ∨ (x - 2) = 2 ∨ (x - 2) = -1 ∨ (x - 2) = -2 := by
      have h7 : (x - 2) ∣ 2 := h5
      have h8 : (x - 2) ≤ 2 := by
        apply Int.le_of_dvd (by norm_num) h7
      have h9 : (x - 2) ≥ -2 := by
        have h10 : -(x - 2) ∣ 2 := by
          exact Int.neg_dvd.2 h7
        have h11 : -(x - 2) ≤ 2 := by
          apply Int.le_of_dvd (by norm_num) h10
        omega
      interval_cases (x - 2) <;> tauto
    rcases h6 with (h7 | h7 | h7 | h7)
    · -- Case (x - 2) = 1.
      have hy : y - 2 = 2 := by
        rw [h7] at h4
        linarith
      have hx : x = 3 := by linarith
      have hy' : y = 4 := by linarith
      rw [hx, hy']
      all_goals norm_num
    · -- Case (x - 2) = 2.
      have hy : y - 2 = 1 := by
        rw [h7] at h4
        linarith
      have hx : x = 4 := by linarith
      have hy' : y = 3 := by linarith
      rw [hx, hy']
      all_goals norm_num
    · -- Case (x - 2) = -1.
      have hy : y - 2 = -2 := by
        rw [h7] at h4
        linarith
      have hx : x = 1 := by linarith
      have hy' : y = 0 := by linarith
      rw [hx, hy']
      all_goals norm_num
    · -- Case (x - 2) = -2.
      have hy : y - 2 = -1 := by
        rw [h7] at h4
        linarith
      have hx : x = 0 := by linarith
      have hy' : y = 1 := by linarith
      rw [hx, hy']
      all_goals norm_num