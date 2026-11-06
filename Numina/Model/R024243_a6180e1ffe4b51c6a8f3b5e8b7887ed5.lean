import Mathlib

theorem algebra_213238 {a : ℝ} (ha : a ≠ 0) (h : a / 2 - 2 / a = 5) :
    (a^12 + 4096) / (64 * a^6) = 19602 := by
  have eq1 : (a^12 + 4096) / (64 * a^6) = (a / 2)^6 + (2 / a)^6 := by
    field_simp [ha]
    <;> ring_nf
  have eq2 : (a / 2)^6 + (2 / a)^6 = 19602 := by
    have h2 : a / 2 - 2 / a = 5 := h
    have h3 : (a / 2) * (2 / a) = 1 := by 
      field_simp [ha]
      <;> nlinarith
    have h4 : (a / 2 + 2 / a)^2 = 29 := by
      have h5 : a / 2 - 2 / a = 5 := h
      have h6 : (a / 2 + 2 / a) ^ 2 = (a / 2 - 2 / a) ^ 2 + 4 * ((a / 2) * (2 / a)) := by 
        nlinarith 
      rw [h6, h5, h3]
      all_goals norm_num
    have h5 : (a / 2)^2 + (2 / a)^2 = 27 := by
      have h6 : (a / 2 + 2 / a)^2 = ( (a / 2)^2 + (2 / a)^2 ) + 2 * ((a / 2) * (2 / a)) := by 
        ring
      rw [h6] at h4
      rw [h3] at h4
      nlinarith
    have h6 : (a / 2)^6 + (2 / a)^6 = 19602 := by
      have h7 : (a / 2)^6 + (2 / a)^6 = ((a / 2)^2 + (2 / a)^2)^3 - 3 * ((a / 2) ^2 * (2 / a)^2) * ((a / 2)^2 + (2 / a)^2) := by 
        ring_nf
      rw [h7, h5]
      have h8 : (a / 2) ^ 2 * (2 / a) ^ 2 = 1 := by 
        calc
          (a / 2) ^ 2 * (2 / a) ^ 2 = ((a / 2) * (2 / a)) ^ 2 := by ring
          _ = 1 ^ 2 := by rw [h3]
          _ = 1 := by norm_num
      rw [h8]
      all_goals norm_num 
    exact h6
  rw [eq1]
  linarith [eq2]