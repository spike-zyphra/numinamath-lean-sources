import Mathlib

theorem inequalities_217956 (x : ℝ) (hx : x ≥ 1) :
    (x - 1) ^ ((1 : ℝ) / 4) + (x + 14) ^ ((1 : ℝ) / 4) ≥ 3 ↔ x ≥ 2 := by
  constructor
  · -- Forward direction: if (x - 1)^(1/4) + (x + 14)^(1/4) ≥ 3 then x ≥ 2
    intro h
    by_contra h1
    push_neg at h1
    have h2 : x < 2 := by linarith
    have h3 : x - 1 < (1 : ℝ) := by linarith
    have h4 : (x - 1 : ℝ) ^ ((1 : ℝ) / 4) < (1 : ℝ) ^ ((1 : ℝ) / 4) := by
      apply Real.rpow_lt_rpow
      all_goals nlinarith
    have h5 : (1 : ℝ) ^ ((1 : ℝ) / 4) = (1 : ℝ) := by
      simp
    have h6 : (x - 1 : ℝ) ^ ((1 : ℝ) / 4) < (1 : ℝ) := by
      linarith [h4, h5]
    have h7 : x + 14 < (16 : ℝ) := by linarith
    have h8 : (x + 14 : ℝ) ^ ((1 : ℝ) / 4) < (16 : ℝ) ^ ((1 : ℝ) / 4) := by
      apply Real.rpow_lt_rpow
      all_goals nlinarith
    have h9 : (16 : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) := by
      have h1 : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
        have h1 : ((16 : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℝ) = (16 : ℝ) := by
          rw [← Real.rpow_mul]
          norm_num
          all_goals linarith
        have h2 : ((2 : ℝ) ^ (4 : ℝ)) = (16 : ℝ) := by norm_num
        have h3 : (2 : ℝ) = ((16 : ℝ) ^ ((1 : ℝ) / 4)) := by
          have h4 : ((2 : ℝ) ^ (4 : ℝ)) = (16 : ℝ) := by norm_num
          have h5 : (2 : ℝ) = ((2 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) := by
            rw [← Real.rpow_mul]
            norm_num
            all_goals nlinarith
          rw [h4] at h5
          linarith
        have h6 : ((16 : ℝ) ^ ((1 : ℝ) / 4)) = (2 : ℝ) := by
          nlinarith [h1, h2, h3]
        linarith [h6]
      linarith [h1]
    have h10 : (x + 14 : ℝ) ^ ((1 : ℝ) / 4) < (2 : ℝ) := by
      nlinarith [h8, h9]
    nlinarith [h6, h10, h]
  · -- Backward direction: if x ≥ 2 then (x - 1)^(1/4) + (x + 14)^(1/4) ≥ 3
    intro h
    have h2 : x - 1 ≥ (1 : ℝ) := by linarith
    have h3 : (x - 1 : ℝ) ^ ((1 : ℝ) / 4) ≥ (1 : ℝ) ^ ((1 : ℝ) / 4) := by
      apply Real.rpow_le_rpow
      all_goals nlinarith
    have h4 : (1 : ℝ) ^ ((1 : ℝ) / 4) = (1 : ℝ) := by
      simp
    have h5 : (x - 1 : ℝ) ^ ((1 : ℝ) / 4) ≥ (1 : ℝ) := by
      linarith [h3, h4]
    have h6 : x + 14 ≥ (16 : ℝ) := by linarith
    have h7 : (x + 14 : ℝ) ^ ((1 : ℝ) / 4) ≥ (16 : ℝ) ^ ((1 : ℝ) / 4) := by
      apply Real.rpow_le_rpow
      all_goals nlinarith
    have h8 : (16 : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) := by
      have h1 : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
        have h1 : ((16 : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℝ) = (16 : ℝ) := by
          rw [← Real.rpow_mul]
          norm_num
          all_goals linarith
        have h2 : ((2 : ℝ) ^ (4 : ℝ)) = (16 : ℝ) := by norm_num
        have h3 : (2 : ℝ) = ((16 : ℝ) ^ ((1 : ℝ) / 4)) := by
          have h4 : ((2 : ℝ) ^ (4 : ℝ)) = (16 : ℝ) := by norm_num
          have h5 : (2 : ℝ) = ((2 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) := by
            rw [← Real.rpow_mul]
            norm_num
            all_goals nlinarith
          rw [h4] at h5
          linarith
        have h6 : ((16 : ℝ) ^ ((1 : ℝ) / 4)) = (2 : ℝ) := by
          nlinarith [h1, h2, h3]
        linarith [h6]
      linarith [h1]
    have h9 : (x + 14 : ℝ) ^ ((1 : ℝ) / 4) ≥ (2 : ℝ) := by
      nlinarith [h7, h8]
    linarith [h5, h9]