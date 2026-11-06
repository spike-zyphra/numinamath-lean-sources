import Mathlib

theorem algebra_190844 (a : ℝ) (ha : a = 9 ^ ((1 : ℝ) / 3) + 3 ^ ((1 : ℝ) / 3) + 1) :
    8 / a^3 + 12 / a^2 + 6 / a + 4 = 6 := by
  have ha1 : a = 1 + (3 : ℝ) ^ ((1 : ℝ) / 3) + (9 : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [ha]
    ring
  have h9 : (9 : ℝ) ^ ((1 : ℝ) / 3) = ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
    have h91 : (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) := by
      norm_num
    rw [h91]
    have h93 : ((3 : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 3) = (3 : ℝ) ^ (2 * (1 / 3 : ℝ)) := by 
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h94 : (3 : ℝ) ^ (2 * (1 / 3 : ℝ)) = ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
      have h10 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = (3 : ℝ) ^ (2 * (1 / 3 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring_nf
        all_goals linarith
      linarith
    rw [h93, h94]
  have hx0 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith
  have ha2 : a - 1 = (3 : ℝ) ^ ((1 : ℝ) / 3) + ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
    rw [ha1]
    nlinarith [h9]
  have ha3 : (a - 1) ^ 3 = 12 + 9 * (a - 1) := by
    rw [ha2]
    have hx : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 3 := by
      have hx0 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals linarith
      linarith
    have h12 : (( (3 : ℝ) ^ ((1 : ℝ) / 3) ) + ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2) ^ 3 = 
        ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 + 3 * ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 4 + 3 * ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 5 + ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 6 := by 
      ring_nf
    have h13 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 4 = 3 * ((3 : ℝ) ^ ((1 : ℝ) / 3)) := by 
      calc
        ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 4 = ((3 : ℝ) ^ ((1 : ℝ) / 3)) * ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by ring
        _ = ((3 : ℝ) ^ ((1 : ℝ) / 3)) * 3 := by rw [hx]
        _ = 3 * ((3 : ℝ) ^ ((1 : ℝ) / 3)) := by ring
    have h14 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 5 = 3 * ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
      calc
        ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 5 = ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 * ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by ring
        _ = ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 * 3 := by rw [hx]
        _ = 3 * ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by ring
    have h15 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 6 = 9 := by
      calc
        ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 6 = (( (3 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3) ^ 2 := by ring
        _ = (3) ^ 2 := by rw [hx]
        _ = (9 : ℝ) := by norm_num
    rw [h13, h14, h15, hx] at h12
    nlinarith [show (( (3 : ℝ) ^ ((1 : ℝ) / 3) ) + ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2) = a - 1 by linarith [ha2] ]
  have ha4 : a ^ 3 = 3 * a ^ 2 + 6 * a + 4 := by
    nlinarith [ha3]
  have ha5 : a ≠ 0 := by
    rw [ha1]
    have h90 : (3 : ℝ) ^ ((1 : ℝ) / 3) > 0 := by
      apply Real.rpow_pos_of_pos
      all_goals
        linarith
    have h91 : (9 : ℝ) ^ ((1 : ℝ) / 3) > 0 := by
      apply Real.rpow_pos_of_pos
      all_goals
        linarith
    positivity
  have ha6 : 8 / a^3 + 12 / a^2 + 6 / a + 4 = (4 * a^3 + 6 * a^2 + 12 * a + 8) / a^3 := by
    field_simp [ha5]
    ring
  have ha7 : 4 * a ^ 3 + 6 * a ^ 2 + 12 * a + 8 = 6 * (a ^ 3) := by
    nlinarith [ha4]
  have ha12 : a ^ 3 ≠ 0 := by
    have ha5' : a ≠ 0 := ha5
    intro h
    have : a = 0 := by
      have h9 : a ^ 3 = 0 := by
        linarith
      have : a = 0 := by
        have h9 : a ^ 3 = 0 := h9
        simp at h9 ⊢
        all_goals 
          try tauto
      assumption
    contradiction
  rw [ha6, ha7]
  field_simp [ha12]