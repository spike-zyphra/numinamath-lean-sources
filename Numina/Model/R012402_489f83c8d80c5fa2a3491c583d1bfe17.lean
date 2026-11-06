import Mathlib

open Real

theorem algebra_98260 : (sqrt (sqrt 5 + 2) + sqrt (sqrt 5 - 2)) / sqrt (sqrt 5 + 1) - sqrt (3 - 2 * sqrt 2) = 1 := by
  have h1 : sqrt (3 - 2 * sqrt 2) = sqrt 2 - 1 := by
    have h2 : (sqrt 2 - 1 : ℝ) ^ 2 = (3 - 2 * sqrt 2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h3 : sqrt (3 - 2 * sqrt 2) = sqrt ((sqrt 2 - 1 : ℝ) ^ 2) := by
      rw [show (3 - 2 * sqrt 2 : ℝ) = (sqrt 2 - 1 : ℝ) ^ 2 by linarith [h2]]
    rw [h3]
    have h4 : sqrt ((sqrt 2 - 1 : ℝ) ^ 2) = abs (sqrt 2 - 1 : ℝ) := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h4]
    have h5 : abs (sqrt 2 - 1 : ℝ) = sqrt 2 - 1 := by
      apply abs_of_nonneg
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h5]
  have h2 : (sqrt (sqrt 5 + 2) + sqrt (sqrt 5 - 2)) ^ 2 = 2 * (sqrt 5 + 1 : ℝ):= by
    have ha1 : 0 ≤ sqrt 5 + 2 := by positivity
    have ha2 : 0 ≤ sqrt 5 - 2 := by
      have h4 : sqrt 5 ≥ 2 := by
        have h5 : sqrt 5 ≥ sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
        have h2 : sqrt 4 = 2 := Real.sqrt_eq_cases.2 (by norm_num)
        nlinarith [Real.sqrt_pos.mpr (show 0 < 5 by norm_num)]
      linarith
    have h3 : sqrt (sqrt 5 + 2) ^ 2 = sqrt 5 + 2 := by
      rw [Real.sq_sqrt]
      linarith
    have h4 : sqrt (sqrt 5 - 2) ^ 2 = sqrt 5 - 2 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h5 : sqrt (sqrt 5 + 2) * sqrt (sqrt 5 - 2) = 1 := by
      have h8 : (sqrt (sqrt 5 + 2) * sqrt (sqrt 5 - 2)) ^ 2 = (1 : ℝ):= by
        calc
          (sqrt (sqrt 5 + 2) * sqrt (sqrt 5 - 2)) ^ 2 = (sqrt (sqrt 5 + 2) ) ^ 2 * (sqrt (sqrt 5 - 2)) ^ 2 := by ring_nf
          _ = (sqrt 5 + 2) * (sqrt 5 - 2) := by
            rw [h3, h4]
          _ = (1 : ℝ) := by
            nlinarith [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
      have h11 : sqrt (sqrt 5 + 2) * sqrt (sqrt 5 - 2) = 1 := by
        nlinarith [show 0 ≤ sqrt (sqrt 5 + 2) * sqrt (sqrt 5 - 2) by positivity, h8]
      linarith
    nlinarith [sq_nonneg (sqrt (sqrt 5 + 2) - sqrt (sqrt 5 - 2)), Real.sqrt_nonneg (sqrt 5 + 2), Real.sqrt_nonneg (sqrt 5 - 2), Real.sqrt_nonneg (sqrt 5 : ℝ), h5]
  have hA : ((sqrt (sqrt 5 + 2 : ℝ) + sqrt (sqrt 5 - 2 : ℝ) ) / sqrt (sqrt 5 + 1 : ℝ) ) ^ 2 = (2 : ℝ):= by
    have h10 : (sqrt (sqrt 5 + 2 : ℝ) + sqrt (sqrt 5 - 2 : ℝ) ) ^ 2 = 2 * (sqrt 5 + 1 : ℝ) := h2
    have h11 : ((sqrt (sqrt 5 + 2 : ℝ) + sqrt (sqrt 5 - 2 : ℝ) ) / sqrt (sqrt 5 + 1 : ℝ) ) ^ 2 = ((sqrt (sqrt 5 + 2 : ℝ) + sqrt (sqrt 5 - 2 : ℝ) ) ^ 2) / (sqrt (sqrt 5 + 1 : ℝ) ^ 2) := by
      field_simp
    have h12 : sqrt (sqrt 5 + 1 : ℝ) ^ 2 = sqrt 5 + 1 := by
      rw [Real.sq_sqrt]
      positivity
    rw [h11, h10, h12]
    <;> field_simp
  have h8 : 0 ≤ (sqrt (sqrt 5 + 2 : ℝ) + sqrt (sqrt 5 - 2 : ℝ) ) / sqrt (sqrt 5 + 1 : ℝ) := by
    apply div_nonneg
    all_goals
      positivity
  have h9 : (sqrt (sqrt 5 + 2 : ℝ) + sqrt (sqrt 5 - 2 : ℝ) ) / sqrt (sqrt 5 + 1 : ℝ) = Real.sqrt 2 := by
    have heq : ((sqrt (sqrt 5 + 2 : ℝ) + sqrt (sqrt 5 - 2 : ℝ) ) / sqrt (sqrt 5 + 1 : ℝ) ) ^ 2 = (2 : ℝ) := hA
    have h12 : (0 : ℝ) ≤ (sqrt (sqrt 5 + 2 : ℝ) + sqrt (sqrt 5 - 2 : ℝ) ) / sqrt (sqrt 5 + 1 : ℝ) := h8
    have h13 : Real.sqrt ( (2 : ℝ) ) = Real.sqrt (2 : ℝ) := by rfl
    have h14 : Real.sqrt ( ((sqrt (sqrt 5 + 2 : ℝ) + sqrt (sqrt 5 - 2 : ℝ) ) / sqrt (sqrt 5 + 1 : ℝ) ) ^ 2 ) = ( (sqrt (sqrt 5 + 2 : ℝ) + sqrt (sqrt 5 - 2 : ℝ) ) / sqrt (sqrt 5 + 1 : ℝ) ) := by
      rw [Real.sqrt_sq (by nlinarith [h8] ) ]
    have h15 : Real.sqrt ( ((sqrt (sqrt 5 + 2 : ℝ) + sqrt (sqrt 5 - 2 : ℝ) ) / sqrt (sqrt 5 + 1 : ℝ) ) ^ 2 ) = Real.sqrt ( (2 : ℝ) ) := by
      rw [heq]
    nlinarith
  rw [h9, h1]
  <;> nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]