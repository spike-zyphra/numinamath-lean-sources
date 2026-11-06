import Mathlib

theorem algebra_213624 {m n p : ℝ}
    (hm : m = ((1 / 3) : ℝ) ^ ((1 : ℝ) / 5))
    (hn : n = ((1 / 4) : ℝ) ^ ((1 : ℝ) / 3))
    (hp : p = ((1 / 5) : ℝ) ^ ((1 : ℝ) / 4)) :
    n < p ∧ p < m := by
  have hn_lt_p : n < p := by
    rw [hn, hp]
    have h1 : ((1 / 4 : ℝ) ^ ((1 : ℝ) / 3)) < ((1 / 5 : ℝ) ^ ((1 : ℝ) / 4)) := by
      have h2 : (( (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ (12 : ℝ) < (( (1 / 5 : ℝ) ^ ((1 : ℝ) / 4) ) ) ^ (12 : ℝ) := by
        have h3 : (( (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) ) ) ^ (12 : ℝ) = ((1 / 4 : ℝ) ^ (4 : ℝ)) := by
          rw [← Real.rpow_mul]
          norm_num
          all_goals norm_num
        have h4 : (( (1 / 5 : ℝ) ^ ((1 : ℝ) / 4) ) ) ^ (12 : ℝ) = ((1 / 5 : ℝ) ^ (3 : ℝ)) := by
          rw [← Real.rpow_mul]
          norm_num
          all_goals norm_num
        rw [h3, h4]
        norm_num
      have h3 : ( (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) ) > 0 := by
        positivity
      have h4 : ( (1 / 5 : ℝ) ^ ((1 : ℝ) / 4) ) > 0 := by
        positivity
      by_contra h
      push_neg at h
      have h5 : ( ( (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) ) ) ≥ ( ( (1 / 5 : ℝ) ^ ((1 : ℝ) / 4) ) ) := by linarith
      have h6 : ( ( ( (1 / 4 : ℝ) ^ ((1 : ℝ) / 3) ) ) ) ^ (12 : ℝ) ≥ ( ( ( (1 / 5 : ℝ) ^ ((1 : ℝ) / 4) ) ) ) ^ (12 : ℝ) := by
        apply Real.rpow_le_rpow
        linarith
        linarith
        norm_num
      linarith
    linarith
  have hp_lt_m : p < m := by
    rw [hp, hm]
    have h1 : ((1 / 5 : ℝ) ^ ((1 : ℝ) / 4)) < ((1 / 3 : ℝ) ^ ((1 : ℝ) / 5)) := by
      have h2 : (( (1 / 5 : ℝ) ^ ((1 : ℝ) / 4) ) ) ^ (20 : ℝ) < (( (1 / 3 : ℝ) ^ ((1 : ℝ) / 5) ) ) ^ (20 : ℝ) := by
        have h3 : (( (1 / 5 : ℝ) ^ ((1 : ℝ) / 4) ) ) ^ (20 : ℝ) = ((1 / 5 : ℝ) ^ (5 : ℝ)) := by
          rw [← Real.rpow_mul]
          norm_num
          all_goals norm_num
        have h4 : (( (1 / 3 : ℝ) ^ ((1 : ℝ) / 5) ) ) ^ (20 : ℝ) = ((1 / 3 : ℝ) ^ (4 : ℝ)) := by
          rw [← Real.rpow_mul]
          norm_num
          all_goals norm_num
        rw [h3, h4]
        norm_num
      have h3 : ( (1 / 5 : ℝ) ^ ((1 : ℝ) / 4) ) > 0 := by
        positivity
      have h4 : ( (1 / 3 : ℝ) ^ ((1 : ℝ) / 5) ) > 0 := by
        positivity
      by_contra h
      push_neg at h
      have h5 : ( ( (1 / 5 : ℝ) ^ ((1 : ℝ) / 4) ) ) ≥ ( ( (1 / 3 : ℝ) ^ ((1 : ℝ) / 5) ) ) := by linarith
      have h6 : ( ( ( (1 / 5 : ℝ) ^ ((1 : ℝ) / 4) ) ) ) ^ (20 : ℝ) ≥ ( ( ( (1 / 3 : ℝ) ^ ((1 : ℝ) / 5) ) ) ) ^ (20 : ℝ) := by
        apply Real.rpow_le_rpow
        linarith
        linarith
        norm_num
      linarith
    linarith
  constructor
  · exact hn_lt_p
  · exact hp_lt_m