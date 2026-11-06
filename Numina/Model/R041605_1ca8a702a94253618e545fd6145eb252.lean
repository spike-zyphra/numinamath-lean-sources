import Mathlib

theorem algebra_10341 (x : ℝ) :
  let cbrt x := if x ≥ 0 then x ^ (1 / 3 : ℝ) else -(-x) ^ (1 / 3 : ℝ)
  cbrt (3 - x) = -3 / 2 ↔ x = 51 / 8 := by
  constructor
  · -- Assume cbrt (3 - x) = -3 / 2, prove x = 51 / 8
    intro h
    by_cases h1 : (3 - x : ℝ) ≥ 0
    · -- Case where 3 - x ≥ 0, so cbrt(3 - x) = (3 - x)^(1/3)
      have h2 : (3 - x : ℝ) ≥ 0 := h1
      have h3 : (3 - x : ℝ) ^ (1 / 3 : ℝ) = -3 / 2 := by
        simpa [h1] using h
      have h4 : (( (3 - x : ℝ) ^ (1 / 3 : ℝ) ) ) ^ 3 = ( -3 / 2 ) ^ 3 := by
        rw [h3]
      have h5 : (( (3 - x : ℝ) ^ (1 / 3 : ℝ) ) ) ^ 3 = (3 - x : ℝ) := by
        have h6 : (( (3 - x : ℝ) ^ (1 / 3 : ℝ) ) ) ^ 3 = (3 - x : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals linarith
        linarith
      have h7 : ( -3 / 2 : ℝ ) ^ 3 = ( -27 / 8 : ℝ ) := by
        norm_num
      have h8 : (3 - x : ℝ) = ( -27 / 8 : ℝ ) := by
        linarith [h4, h5, h7]
      have h9 : x = ( 51 / 8 : ℝ ) := by
        linarith
      linarith
    · -- Case where 3 - x < 0, so cbrt(3 - x) = -(- (3 - x))^(1/3)
      have h10 : (3 - x : ℝ) < 0 := by
        by_contra h11
        push_neg at h11
        have h12 : (3 - x : ℝ) ≥ 0 := by linarith
        contradiction
      have h3 : - ( ( - (3 - x : ℝ) ) ^ (1 / 3 : ℝ) ) = -3 / 2 := by
        simp [show ¬ (3 - x : ℝ) ≥ 0 by linarith] at h ⊢
        all_goals linarith
      have h4 : ( ( - (3 - x : ℝ) ) ^ (1 / 3 : ℝ) ) = 3 / 2 := by
        linarith [h3]
      have h4' : ( ( - (3 - x : ℝ) ) ^ (1 / 3 : ℝ) ) ^ 3 = ( 3 / 2 ) ^ 3 := by
        rw [h4]
      have h7 : ( ( - (3 - x : ℝ) ) ^ (1 / 3 : ℝ) ) ^ 3 = ( - (3 - x : ℝ) ) := by
        have h8 : ( ( - (3 - x : ℝ) ) ^ (1 / 3 : ℝ) ) ^ 3 = ( - (3 - x : ℝ) ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals linarith
        linarith
      have h8 : ( 3 / 2 : ℝ ) ^ 3 = ( 27 / 8 : ℝ ) := by
        norm_num
      have h9 : - (3 - x : ℝ) = (27 / 8 : ℝ) := by
        linarith [h4', h7, h8]
      have h10 : x = (51 / 8 : ℝ) := by
        linarith
      linarith
  · -- Assume x = 51 / 8, prove cbrt (3 - x) = -3 / 2
    intro h
    rw [h]
    norm_num [show (3 - (51 / 8 : ℝ) : ℝ) < (0 : ℝ) by norm_num]
    all_goals
      have h6 : ( (27 / 8 : ℝ) ) ^ (1 / 3 : ℝ) = ( 3 / 2 : ℝ ) := by
        have h7 : ( (27 / 8 : ℝ) ) ^ (1 / 3 : ℝ) = ( 3 / 2 : ℝ ) := by
          rw [show (27 / 8 : ℝ) = (3 / 2 : ℝ) ^ (3 : ℝ) by norm_num]
          rw [← Real.rpow_mul]
          norm_num
          all_goals norm_num
        linarith
      linarith [h6]