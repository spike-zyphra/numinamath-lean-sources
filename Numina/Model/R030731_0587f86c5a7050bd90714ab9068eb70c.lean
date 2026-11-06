import Mathlib

theorem algebra_234887 {x y z : ℤ} (h1 : x + y - 2018 = (x - 2019) * y) (h2 : x + z - 2014 = (x - 2019) * z) (h3 : y + z + 2 = y * z) :
    (x = 2022 ∧ y = 2 ∧ z = 4) ∨ (x = 2018 ∧ y = 0 ∧ z = -2) := by
  have h4 : (y - 1) * (z - 1) = 3 := by
    nlinarith
  have h5 : (y - 1) = 1 ∨ (y - 1) = 3 ∨ (y - 1) = -1 ∨ (y - 1) = -3 := by
    have h6 : (y - 1) * (z - 1) = 3 := h4
    have h7 : (y - 1) ∣ 3 := by
      use (z - 1)
      all_goals linarith
    have h8 : (y - 1) = 1 ∨ (y - 1) = 3 ∨ (y - 1) = -1 ∨ (y - 1) = -3 := by
      have h9 : (y - 1) ≤ 3 := by
        apply Int.le_of_dvd (by norm_num) h7
      have h10 : (y - 1) ≥ -3 := by
        have h11 : (- (y - 1)) ∣ 3 := by
          exact Int.neg_dvd.2 h7
        have h12 : - (y - 1) ≤ 3 := by
          apply Int.le_of_dvd (by norm_num) h11
        omega
      interval_cases (y - 1) <;> tauto
    assumption
  rcases h5 with (h51 | h52 | h53 | h54)
  · -- case y - 1 = 1, so y = 2
    have h61 : y = 2 := by linarith
    have h62 : z - 1 = 3 := by
      rw [show y - 1 = 1 by linarith] at h4
      linarith
    have h63 : z = 4 := by linarith
    have h64 : x = 2022 := by 
      rw [h61] at h1
      linarith
    left
    constructor
    · exact h64
    constructor
    · exact h61
    · exact h63
  · -- case y - 1 = 3, so y = 4
    have h71 : y = 4 := by linarith
    have h72 : z - 1 = 1 := by
      rw [show y - 1 = 3 by linarith] at h4
      linarith
    have h73 : z = 2 := by linarith
    rw [h71] at h1
    nlinarith
  · -- case y - 1 = -1, so y = 0
    have h81 : y = 0 := by linarith
    have h82 : z - 1 = -3 := by
      rw [show y - 1 = -1 by linarith] at h4
      linarith
    have h83 : z = -2 := by linarith
    have h84 : x = 2018 := by 
      rw [h81] at h1
      nlinarith
    right
    constructor
    · exact h84
    constructor
    · exact h81
    · exact h83
  · -- case y - 1 = -3, so y = -2
    have h91 : y = -2 := by linarith
    have h92 : z - 1 = -1 := by
      rw [show y - 1 = -3 by linarith] at h4
      linarith
    have h93 : z = 0 := by linarith
    rw [h91] at h1
    nlinarith