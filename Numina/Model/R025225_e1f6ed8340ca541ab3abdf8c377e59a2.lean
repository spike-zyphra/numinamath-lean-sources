import Mathlib

open Real

theorem algebra_182618 {s : ℝ}
    (hs : s = (20 + 14 * sqrt 2) ^ ((1 : ℝ) / 3) + (20 - 14 * sqrt 2) ^ ((1 : ℝ) / 3)) :
    s ^ 2 = 16 ∧ s ^ 3 = 64 ∧ ∃ q : ℚ, s = q := by

  have h1 : ((20 + 14 * sqrt 2) : ℝ) = (2 + Real.sqrt 2) ^ 3 := by
    ring_nf
    have hsqrt2 : (sqrt 2 : ℝ) ^ 2 = 2 := by
      exact Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hsqrt22 : (sqrt 2 : ℝ) ^ 4 = 4 := by
      calc
        (sqrt 2 : ℝ) ^ 4 = ((sqrt 2 : ℝ) ^ 2) ^ 2 := by ring
        _ = 4 := by 
          rw [hsqrt2]
          norm_num
    nlinarith [hsqrt22]

  have h2 : ((20 - 14 * sqrt 2) : ℝ) = (2 - Real.sqrt 2) ^ 3 := by
    ring_nf
    have hsqrt2 : (sqrt 2 : ℝ) ^ 2 = 2 := by
      exact Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hsqrt22 : (sqrt 2 : ℝ) ^ 4 = 4 := by
      calc
        (sqrt 2 : ℝ) ^ 4 = ((sqrt 2 : ℝ) ^ 2) ^ 2 := by ring
        _ = 4 := by 
          rw [hsqrt2]
          norm_num
    nlinarith [hsqrt22]

  have h3 : ((20 + 14 * sqrt 2 : ℝ) ^ ((1 : ℝ) / 3)) = (2 + Real.sqrt 2) := by
    rw [h1]
    have h4 : ((2 + Real.sqrt 2) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = (2 + Real.sqrt 2) := by
      have h5 : ((2 + Real.sqrt 2 : ℝ) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = (2 + Real.sqrt 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          have h6 : (2 + Real.sqrt 2 : ℝ) ≥ 0 := by
            nlinarith [Real.sqrt_pos.mpr (show (2: ℝ) > 0 by norm_num : (2: ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          positivity
      linarith
    linarith

  have h4 : ((20 - 14 * sqrt 2 : ℝ) ^ ((1 : ℝ) / 3)) = (2 - Real.sqrt 2) := by
    rw [h2]
    have h5 : ((2 - Real.sqrt 2) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = (2 - Real.sqrt 2) := by
      have h6 : ((2 - Real.sqrt 2 : ℝ) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = (2 - Real.sqrt 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          have h7 : (2 - Real.sqrt 2 : ℝ) ≥ 0 := by
            nlinarith [Real.sqrt_pos.mpr (show (2: ℝ) > 0 by norm_num : (2: ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          positivity
      linarith
    linarith

  have h5 : s = 4 := by
    rw [hs]
    rw [h3, h4]
    ring_nf
    <;> nlinarith [Real.sqrt_pos.mpr (show (2: ℝ) > 0 by norm_num : (2: ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  constructor
  · -- Show s^2 = 16
    rw [h5]
    norm_num

  constructor
  · -- Show s^3 = 64
    rw [h5]
    norm_num

  · -- Show ∃ q : ℚ, s = q
    use (4 : ℚ)
    rw [h5]
    all_goals norm_num