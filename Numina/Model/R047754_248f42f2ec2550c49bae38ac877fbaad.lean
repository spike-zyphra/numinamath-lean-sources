import Mathlib

theorem algebra_285035 (θ : ℝ) (h : Real.sin θ - Real.cos θ = (Real.sqrt 6 - Real.sqrt 2) / 2) :
    24 * (Real.sin θ ^ 3 - Real.cos θ ^ 3) ^ 2 = 12 := by

  have h1 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ

  have eq2 : (Real.sin θ - Real.cos θ) ^ 2 = ((Real.sqrt 6 - Real.sqrt 2) / 2) ^ 2 := by
    rw [h]

  have eq3 : (Real.sin θ - Real.cos θ) ^ 2 = Real.sin θ ^ 2 + Real.cos θ ^ 2 - 2 * (Real.sin θ * Real.cos θ) := by
    ring

  have eq4 : ((Real.sqrt 6 - Real.sqrt 2) / 2) ^ 2 = 2 - Real.sqrt 3 := by
    have h1 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h3 : Real.sqrt 6 * Real.sqrt 2 = 2 * Real.sqrt 3 := by
      calc
        Real.sqrt 6 * Real.sqrt 2 = Real.sqrt (6 * 2) := by rw [Real.sqrt_mul (by norm_num)]
        _ = Real.sqrt 12 := by norm_num
        _ = Real.sqrt (4 * 3) := by norm_num
        _ = Real.sqrt 4 * Real.sqrt 3 := by rw [Real.sqrt_mul (by norm_num)]
        _ = (2 : ℝ) * Real.sqrt 3 := by
          have h4 : Real.sqrt 4 = (2 : ℝ) := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h4]
          all_goals ring
    nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h3]

  have eq5 : (Real.sin θ - Real.cos θ) ^ 2 = 1 - 2 * (Real.sin θ * Real.cos θ) := by
    rw [eq3]
    have h2 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := by
      linarith [h1]
    linarith [h2]

  have eq6 : (1 - 2 * (Real.sin θ * Real.cos θ) ) = (2 - Real.sqrt 3) := by
    linarith [ eq5, eq4, eq2 ]

  have eq7 : Real.sin θ * Real.cos θ = (Real.sqrt 3 - 1) / 2 := by
    nlinarith [eq6]

  have eq8 : Real.sin θ ^ 3 - Real.cos θ ^ 3 = (Real.sin θ - Real.cos θ) * (Real.sin θ ^ 2 + Real.sin θ * Real.cos θ + Real.cos θ ^ 2) := by
    ring

  have eq9 : Real.sin θ ^ 2 + Real.sin θ * Real.cos θ + Real.cos θ ^ 2 = (1 + (Real.sin θ * Real.cos θ)) := by
    have h2 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := by
      linarith [h1]
    nlinarith [h2, eq7]

  have eq10 : Real.sin θ ^ 3 - Real.cos θ ^ 3 = ( (Real.sqrt 6 - Real.sqrt 2) / 2 ) * ( 1 + (Real.sqrt 3 - 1) / 2 ) := by
    rw [eq8, eq9, h, eq7]

  have eq11 : (Real.sin θ ^ 3 - Real.cos θ ^ 3) ^ 2 = (( (Real.sqrt 6 - Real.sqrt 2) / 2 ) * ( 1 + (Real.sqrt 3 - 1) / 2 )) ^ 2 := by
    rw [eq10]

  rw [eq11]

  have eq12 : (( (Real.sqrt 6 - Real.sqrt 2) / 2 ) * ( 1 + (Real.sqrt 3 - 1) / 2 )) ^ 2 = ((Real.sqrt 6 - Real.sqrt 2) * (1 + Real.sqrt 3)) ^ 2 / 16 := by
    ring_nf

  rw [eq12]

  have eq14 : ((Real.sqrt 6 - Real.sqrt 2) * (1 + Real.sqrt 3)) ^ 2 = 8 := by
    have h1 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h3 : Real.sqrt 6 * Real.sqrt 2 = 2 * Real.sqrt 3 := by
      calc
        Real.sqrt 6 * Real.sqrt 2 = Real.sqrt (6 * 2) := by rw [Real.sqrt_mul (by norm_num)]
        _ = Real.sqrt 12 := by norm_num
        _ = Real.sqrt (4 * 3) := by norm_num
        _ = Real.sqrt 4 * Real.sqrt 3 := by rw [Real.sqrt_mul (by norm_num)]
        _ = (2 : ℝ) * Real.sqrt 3 := by
          have h4 : Real.sqrt 4 = (2 : ℝ) := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h4]
          all_goals ring
    nlinarith [ Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h3 ]

  rw [eq14]
  <;> norm_num