import Mathlib

open Real

theorem inequalities_227533 {a b c : ℝ}
    (ha : a = ((1 : ℝ) / 2) ^ ((1 : ℝ) / 4))
    (hb : b = ((1 : ℝ) / 3) ^ ((1 : ℝ) / 2))
    (hc : c = ((1 : ℝ) / 4) ^ ((1 : ℝ) / 3)) :
    b < c ∧ c < a := by
  have h1 : b < c := by
    rw [hb, hc]
    have h2 : ((1 / 3 : ℝ) ^ ((1 : ℝ) / 2)) < ((1 / 4 : ℝ) ^ ((1 : ℝ) / 3)) := by
      have h3 : (( (1 / 3 : ℝ) ^ ((1 : ℝ) / 2) ) ^ 6 < (( (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 6) ) := by
        have h4 : (( (1 / 3 : ℝ) ^ ((1 : ℝ) / 2) ) ^ 6 = (1 / 3 : ℝ) ^ (3 : ℝ) ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals norm_num
        have h5 : (( (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 6 = (1 / 4 : ℝ) ^ (2 : ℝ) ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals norm_num
        rw [h4, h5]
        norm_num
      have h6 : ( (1 / 3 : ℝ) ^ ((1 : ℝ) / 2) ) ≥ 0 := by positivity
      have h7 : ( (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) ) ≥ 0 := by positivity
      have h8 : ( (1 / 3 : ℝ) ^ ((1 : ℝ) / 2) ) < ( (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) ) := by
        by_contra h
        push_neg at h
        have h9 : ( ( (1 / 3 : ℝ) ^ ((1 : ℝ) / 2) ) ) ≥ ( ( (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) ) ) := by linarith
        have h10 : ( ( (1 / 3 : ℝ) ^ ((1 : ℝ) / 2) ) ) ^ 6 ≥ ( ( (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ 6 := by
          apply pow_le_pow_left
          all_goals
            try linarith
            try positivity
        linarith
      linarith
    linarith
  have h2 : c < a := by
    rw [hc, ha]
    have h3 : ((1 / 4 : ℝ) ^ ((1 : ℝ) / 3)) < ((1 / 2 : ℝ) ^ ((1 : ℝ) / 4)) := by
      have h4 : (( (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 12 < (( (1 / 2 : ℝ) ^ ((1 : ℝ) / 4) ) ^ 12 ) ) := by
        have h5 : (( (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) ) ^ 12 = (1 / 4 : ℝ) ^ (4 : ℝ) ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals norm_num
        have h6 : (( (1 / 2 : ℝ) ^ ((1 : ℝ) / 4) ) ^ 12 = (1 / 2 : ℝ) ^ (3 : ℝ) ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals norm_num
        rw [h5, h6]
        norm_num
      have h7 : ( (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) ) ≥ 0 := by positivity
      have h8 : ( (1 / 2 : ℝ) ^ ((1 : ℝ) / 4) ) ≥ 0 := by positivity
      have h9 : ( (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) ) < ( (1 / 2 : ℝ) ^ ((1 : ℝ) / 4) ) := by
        by_contra h
        push_neg at h
        have h10 : ( ( (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) ) ) ≥ ( ( (1 / 2 : ℝ) ^ ((1 : ℝ) / 4) ) ) := by linarith
        have h11 : ( ( (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ 12 ≥ ( ( (1 / 2 : ℝ) ^ ((1 : ℝ) / 4) ) ) ^ 12 := by
          apply pow_le_pow_left
          all_goals
            try linarith
            try positivity
        linarith
      linarith
    linarith
  constructor
  · exact h1
  · exact h2