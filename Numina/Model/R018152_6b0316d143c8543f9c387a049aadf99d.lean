import Mathlib

theorem algebra_193257 (x y z : ℤ) (h1 : x^2 - y^2 - z^2 = 1) (h2 : y + z - x = 3) :
    (x = 9 ∧ y = 8 ∧ z = 4) ∨ (x = -3 ∧ y = -2 ∧ z = 2) ∨
    (x = 9 ∧ y = 4 ∧ z = 8) ∨ (x = -3 ∧ y = 2 ∧ z = -2) := by

  have h3 : x = y + z - 3 := by linarith
  rw [h3] at h1
  have h4 : (y - 3) * (z - 3) = 5 := by
    nlinarith [h1]

  have h5 : y - 3 ∣ 5 := by
    use z - 3
    linarith

  have h6 : y - 3 = 1 ∨ y - 3 = 5 ∨ y - 3 = -1 ∨ y - 3 = -5 := by
    have h7 : y - 3 ∣ 5 := h5
    have : y - 3 ≤ 5 := by apply Int.le_of_dvd (by norm_num) h7
    have : y - 3 ≥ -5 := by 
      have h8 : -(y - 3) ∣ 5 := by
        exact Int.neg_dvd.2 h7
      have h9 : -(y - 3) ≤ 5 := by
        apply Int.le_of_dvd (by norm_num) h8
      omega
    interval_cases h : y - 3 <;> tauto

  rcases h6 with (h7 | h7 | h7 | h7)
  · -- y - 3 = 1
    have hy1 : y = 4 := by
      linarith
    have h81 : z - 3 = 5 := by
      rw [show y - 3 = 1 by linarith] at h4
      linarith
    have hz1 : z = 8 := by
      linarith
    have hx1 : x = 9 := by
      rw [hy1, hz1] at h3
      linarith
    simp [hx1, hy1, hz1]
  · -- y - 3 = 5
    have hy2 : y = 8 := by
      linarith
    have h82 : z - 3 = 1 := by
      rw [show y - 3 = 5 by linarith] at h4
      linarith
    have hz2 : z = 4 := by
      linarith
    have hx2 : x = 9 := by
      rw [hy2, hz2] at h3
      linarith
    simp [hx2, hy2, hz2]
  · -- y - 3 = -1
    have hy3 : y = 2 := by
      linarith
    have h83 : z - 3 = -5 := by
      rw [show y - 3 = -1 by linarith] at h4
      linarith
    have hz3 : z = -2 := by
      linarith
    have hx3 : x = -3 := by
      rw [hy3, hz3] at h3
      linarith
    simp [hx3, hy3, hz3]
  · -- y - 3 = -5
    have hy4 : y = -2 := by
      linarith
    have h84 : z - 3 = -1 := by
      rw [show y - 3 = -5 by linarith] at h4
      linarith
    have hz4 : z = 2 := by
      linarith
    have hx4 : x = -3 := by
      rw [hy4, hz4] at h3
      linarith
    simp [hx4, hy4, hz4]