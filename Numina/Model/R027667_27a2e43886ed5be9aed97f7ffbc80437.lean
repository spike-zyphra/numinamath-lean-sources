import Mathlib

open Real

theorem algebra_34063 {w : ℝ} (hw : w = sqrt (1 + sqrt (-3 + 2 * sqrt 3)) - sqrt (1 - sqrt (-3 + 2 * sqrt 3))) :
    w = sqrt 3 - 1 := by
  have hw2 : w ^ 2 = (sqrt 3 - 1) ^ 2 := by
    rw [hw]
    have h1 : (sqrt (1 + sqrt (-3 + 2 * sqrt 3)) - sqrt (1 - sqrt (-3 + 2 * sqrt 3)) ) ^ 2 =
        (sqrt (1 + sqrt (-3 + 2 * sqrt 3)) ) ^ 2 + (sqrt (1 - sqrt (-3 + 2 * sqrt 3)) ) ^ 2 - 2 * (sqrt (1 + sqrt (-3 + 2 * sqrt 3)) * sqrt (1 - sqrt (-3 + 2 * sqrt 3)) ) := by
      ring 
    rw [h1]
    have h21 : (sqrt (1 + sqrt (-3 + 2 * sqrt 3)) )^2 = 1 + sqrt (-3 + 2 * sqrt 3) := by 
      apply Real.sq_sqrt
      have h32 : sqrt (-3 + 2 * sqrt 3) ≥ 0 := by positivity
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (-3 + 2 * sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ -3 + 2 * sqrt 3 by 
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (sqrt 3 ^ 2 - 3)]
        ) ]
    have h22 : (sqrt (1 - sqrt (-3 + 2 * sqrt 3)) )^2 = 1 - sqrt (-3 + 2 * sqrt 3) := by 
      apply Real.sq_sqrt
      have h42 : sqrt (-3 + 2 * sqrt 3) ≤ 1 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (-3 + 2 * sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ -3 + 2 * sqrt 3 by 
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (sqrt 3 ^ 2 - 3)]
        ) ]
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (-3 + 2 * sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ -3 + 2 * sqrt 3 by 
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (sqrt 3 ^ 2 - 3)]
        ) ]
    have h33 : sqrt (1 + sqrt (-3 + 2 * sqrt 3)) * sqrt (1 - sqrt (-3 + 2 * sqrt 3)) = Real.sqrt 3 - 1 := by 
      have h37 : sqrt (1 + sqrt (-3 + 2 * sqrt 3)) * sqrt (1 - sqrt (-3 + 2 * sqrt 3)) = 
          Real.sqrt ((1 + sqrt (-3 + 2 * sqrt 3)) * (1 - sqrt (-3 + 2 * sqrt 3)) ) := by 
        calc 
          sqrt (1 + sqrt (-3 + 2 * sqrt 3)) * sqrt (1 - sqrt (-3 + 2 * sqrt 3)) =
              Real.sqrt (1 + sqrt (-3 + 2 * sqrt 3)) * Real.sqrt (1 - sqrt (-3 + 2 * sqrt 3)) := by 
                rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
          _ = Real.sqrt ((1 + sqrt (-3 + 2 * sqrt 3)) * (1 - sqrt (-3 + 2 * sqrt 3)) ) := by
            rw [← Real.sqrt_mul (by 
              have h11 : sqrt (-3 + 2 * sqrt 3) ≥ 0 := by positivity
              nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (-3 + 2 * sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ -3 + 2 * sqrt 3 by 
                nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (sqrt 3 ^ 2 - 3)]
              ) ]
            ) ]
      rw [h37]
      have h38 : (1 + sqrt (-3 + 2 * sqrt 3)) * (1 - sqrt (-3 + 2 * sqrt 3)) = 4 - 2 * Real.sqrt 3 := by
        nlinarith [Real.sqrt_nonneg (-3 + 2 * sqrt 3), Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ -3 + 2 * sqrt 3 by 
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (sqrt 3 ^ 2 - 3)]
        ), sq_nonneg (sqrt 3 - 1) ]
      rw [h38]
      have h39 : Real.sqrt (4 - 2 * Real.sqrt 3) = Real.sqrt 3 - 1 := by 
        have h40 : Real.sqrt 3 - 1 ≥ 0 := by 
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        have h41 : (Real.sqrt 3 - 1) ^ 2 = 4 - 2 * Real.sqrt 3 := by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        rw [←h41]
        field_simp 
      linarith 
    rw [h21, h22, h33]
    all_goals nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (-3 + 2 * sqrt 3) ]
  have hw_pos : 0 ≤ w := by 
    rw [hw]
    have h6 : sqrt (1 + sqrt (-3 + 2 * sqrt 3)) ≥ sqrt (1 - sqrt (-3 + 2 * sqrt 3)) := by 
      apply Real.sqrt_le_sqrt
      have h71 : sqrt (-3 + 2 * sqrt 3) ≥ 0 := by positivity
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg (-3 + 2 * sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ -3 + 2 * sqrt 3 by 
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (sqrt 3 ^ 2 - 3)]
        ), sq_nonneg (sqrt 3 - 1) ]
    have h7 : sqrt (1 - sqrt (-3 + 2 * sqrt 3)) ≥ 0 := by positivity
    linarith [h6, Real.sqrt_nonneg (1 + sqrt (-3 + 2 * sqrt 3)), h7]
  have h81 : w ≥ 0 := hw_pos 
  have h82 : (sqrt 3 - 1) ≥ 0 := by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have hw_eq : w = sqrt 3 - 1 := by
    nlinarith [hw2, hw_pos, h82 ]
  exact hw_eq