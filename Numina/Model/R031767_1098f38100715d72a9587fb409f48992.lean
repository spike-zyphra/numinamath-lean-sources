import Mathlib

theorem inequalities_597589 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a / b) ^ ((1 : ℝ) / 3) + (b / a) ^ ((1 : ℝ) / 3) ≤
    ((2 * (1 + b / a) * (1 + a / b)) ^ ((1 : ℝ) / 3)) := by
  have h1 : 0 < a / b := by
    apply div_pos
    exact ha
    exact hb
  have h2 : 0 < b / a := by
    apply div_pos
    exact hb
    exact ha
  have h3 : ((a / b) ^ ((1 : ℝ) / 3) + (b / a) ^ ((1 : ℝ) / 3)) ^ 3 ≤ 2 * (1 + b / a) * (1 + a / b) := by
    have h4 : ((a / b) ^ ((1 : ℝ) / 3)) ^ 3 = a / b := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith [h1]
    have h5 : ((b / a) ^ ((1 : ℝ) / 3)) ^ 3 = b / a := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith [h2]
    have h6 : ((a / b) ^ ((1 : ℝ) / 3) + (b / a) ^ ((1 : ℝ) / 3)) ^ 3 =
        ((a / b) ^ ((1 : ℝ) / 3)) ^ 3 + ((b / a) ^ ((1 : ℝ) / 3)) ^ 3 + 3 * ((a / b) ^ ((1 : ℝ) / 3) * (b / a) ^ ((1 : ℝ) / 3) * ((a / b) ^ ((1 : ℝ) / 3) + (b / a) ^ ((1 : ℝ) / 3))) := by
      ring
    have h7 : ((a / b) ^ ((1 : ℝ) / 3) * (b / a) ^ ((1 : ℝ) / 3) ) = 1 := by
      have h8 : (a / b) * (b / a) = 1 := by
        field_simp [ha.ne.symm, hb.ne.symm]
      have h9 : ((a / b) ^ ((1 : ℝ) / 3)) * ((b / a) ^ ((1 : ℝ) / 3)) =
          ((a / b) * (b / a)) ^ ((1 : ℝ) / 3) := by
        rw [← Real.mul_rpow]
        all_goals
          nlinarith [h1, h2]
      rw [h9, h8]
      norm_num
    rw [h6, h4, h5, h7]
    have h8 : 2 * (1 + b / a) * (1 + a / b) = 4 + 2 * (a / b + b / a) := by
      field_simp
      <;> ring
    nlinarith [sq_nonneg ( (a / b) ^ ((1 : ℝ) / 3) - (b / a) ^ ((1 : ℝ) / 3) ), sq_nonneg ( (a / b) ^ ((1 : ℝ) / 3) - 1 ), sq_nonneg ( (b / a) ^ ((1 : ℝ) / 3) - 1 ), sq_nonneg ( (a / b) ^ ((1 : ℝ) / 3) + (b / a) ^ ((1 : ℝ) / 3) - 2 ), sq_nonneg ( a - b ), sq_nonneg ( (a / b) - 1 ), sq_nonneg ( (b / a) - 1 ), mul_pos ha hb, mul_pos (show 0 < a / b by positivity) (show 0 < b / a by positivity) ]
  have h4 : ((a / b) ^ ((1 : ℝ) / 3) + (b / a) ^ ((1 : ℝ) / 3)) ≤ ((2 * (1 + b / a) * (1 + a / b)) ^ ((1 : ℝ) / 3)) := by
    have h10 : ((a / b) ^ ((1 : ℝ) / 3) + (b / a) ^ ((1 : ℝ) / 3)) ^ 3 ≤ 2 * (1 + b / a) * (1 + a / b) := h3
    have h11 : (( (2 * (1 + b / a) * (1 + a / b) ) ^ ((1 : ℝ) / 3) ) ) ^ 3 = 2 * (1 + b / a) * (1 + a / b) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        positivity
    have h12 : ((a / b) ^ ((1 : ℝ) / 3) + (b / a) ^ ((1 : ℝ) / 3)) ≤ ((2 * (1 + b / a) * (1 + a / b)) ^ ((1 : ℝ) / 3)) := by
      by_contra h
      push_neg at h
      have h13 : (( (a / b) ^ ((1 : ℝ) / 3) + (b / a) ^ ((1 : ℝ) / 3) ) ) ^ 3 > (( (2 * (1 + b / a) * (1 + a / b)) ^ ((1 : ℝ) / 3) ) ) ^ 3 := by
        have h14 : (( (a / b) ^ ((1 : ℝ) / 3) + (b / a) ^ ((1 : ℝ) / 3) ) ) > (( (2 * (1 + b / a) * (1 + a / b)) ^ ((1 : ℝ) / 3) ) ) := h
        have h15 : (( (a / b) ^ ((1 : ℝ) / 3) + (b / a) ^ ((1 : ℝ) / 3) ) ) ^ 3 > (( (2 * (1 + b / a) * (1 + a / b)) ^ ((1 : ℝ) / 3) ) ) ^ 3 := by
          apply pow_lt_pow_left
          all_goals nlinarith [h14, show 0 < ( (a / b) ^ ((1 : ℝ) / 3) + (b / a) ^ ((1 : ℝ) / 3) ) by positivity, show 0 < ( (2 * (1 + b / a) * (1 + a / b)) ^ ((1 : ℝ) / 3) ) by positivity ]
        linarith
      have h16 : (( (2 * (1 + b / a) * (1 + a / b)) ^ ((1 : ℝ) / 3) ) ) ^ 3 > (( (a / b) ^ ((1 : ℝ) / 3) + (b / a) ^ ((1 : ℝ) / 3) ) ) ^ 3 := by linarith [ h11, h10, h13 ]
      linarith
    linarith
  linarith [h4]