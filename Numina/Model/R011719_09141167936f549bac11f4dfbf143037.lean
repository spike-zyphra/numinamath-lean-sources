import Mathlib

open Real

theorem algebra_278298 :
    (sqrt 2 + sqrt (2 - sqrt 3) - sqrt (2 + sqrt 3)) = 0 ∧
    (sqrt 6 - sqrt (2 - sqrt 3) - sqrt (2 + sqrt 3)) = 0 := by

  have h1 : sqrt 2 + sqrt (2 - sqrt 3) = sqrt (2 + sqrt 3) := by
    have h2 : (sqrt 2 + sqrt (2 - sqrt 3)) ^ 2 = (sqrt (2 + sqrt 3)) ^ 2 := by
      have h3 : (sqrt 2 + sqrt (2 - sqrt 3)) ^ 2 =
        (sqrt 2) ^ 2 + (sqrt (2 - sqrt 3)) ^ 2 + 2 * (sqrt 2 * sqrt (2 - sqrt 3)) := by
        ring
      have h4 : (sqrt (2 + sqrt 3)) ^ 2 = 2 + sqrt 3 := by
        rw [Real.sq_sqrt]
        positivity
      rw [h3, h4]
      have h5 : (sqrt 2) ^ 2 = 2 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      have h6 : (sqrt (2 - sqrt 3)) ^ 2 = 2 - sqrt 3 := by
        rw [Real.sq_sqrt]
        have h3_pos : 0 ≤ (2 - sqrt 3 : ℝ) := by
          have h1 : sqrt 3 ≤ (2 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
          nlinarith [Real.sqrt_nonneg 3]
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h7 : sqrt 2 * sqrt (2 - sqrt 3) = Real.sqrt 3 - 1 := by
        have h8 : sqrt 2 * sqrt (2 - sqrt 3) = Real.sqrt (2 * (2 - sqrt 3)) := by
          rw [← Real.sqrt_mul (by
            have h1 : sqrt 3 ≤ (2 : ℝ) := by
              nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
            have h2 : 0 ≤ (2 - sqrt 3 : ℝ) := by nlinarith [Real.sqrt_nonneg 3]
            all_goals nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
          )
          ]
        rw [h8]
        have h9 : 2 * (2 - sqrt 3) = (Real.sqrt 3 - 1) ^ 2 := by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        rw [h9]
        have h10 : Real.sqrt ((Real.sqrt 3 - 1) ^ 2) = Real.sqrt 3 - 1 := by
          rw [Real.sqrt_sq]
          have h11 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
          have h12 : 1 < Real.sqrt 3 := by
            rw [Real.lt_sqrt] <;> norm_num
          have h13 : (Real.sqrt 3 - 1 : ℝ) ≥ 0 := by
            nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
          linarith
        rw [h10]
      nlinarith [h7, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h10 : (sqrt 2 + sqrt (2 - sqrt 3)) = (sqrt (2 + sqrt 3)) := by
      nlinarith [h2, Real.sqrt_nonneg (2 + sqrt 3), Real.sqrt_nonneg 2, Real.sqrt_nonneg (2 - sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 - sqrt 3 : ℝ) by
        have h1 : sqrt 3 ≤ (2 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
        have h2 : 0 ≤ (2 - sqrt 3 : ℝ) := by nlinarith [Real.sqrt_nonneg 3]
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      )
      ]
    linarith

  have h2 : sqrt 6 = sqrt (2 - sqrt 3) + sqrt (2 + sqrt 3) := by
    have h3 : (sqrt 6) ^ 2 = (sqrt (2 - sqrt 3) + sqrt (2 + sqrt 3)) ^ 2 := by
      have h6 : (sqrt 6) ^ 2 = 6 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      have h7 : (sqrt (2 - sqrt 3) + sqrt (2 + sqrt 3)) ^ 2 =
        (sqrt (2 - sqrt 3)) ^ 2 + (sqrt (2 + sqrt 3)) ^ 2 + 2 * (sqrt (2 - sqrt 3) * sqrt (2 + sqrt 3)) := by
        ring
      have h8 : (sqrt (2 - sqrt 3)) ^ 2 = 2 - sqrt 3 := by
        rw [Real.sq_sqrt]
        have h3_pos : 0 ≤ (2 - sqrt 3 : ℝ) := by
          have h1 : sqrt 3 ≤ (2 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
          nlinarith [Real.sqrt_nonneg 3]
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h9 : (sqrt (2 + sqrt 3)) ^ 2 = 2 + sqrt 3 := by
        rw [Real.sq_sqrt]
        positivity
      have h10 : sqrt (2 - sqrt 3) * sqrt (2 + sqrt 3) = 1 := by
        have h11 : sqrt (2 - sqrt 3) * sqrt (2 + sqrt 3) = Real.sqrt ((2 - sqrt 3) * (2 + sqrt 3)) := by
          rw [← Real.sqrt_mul (by
            have h1 : sqrt 3 ≤ (2 : ℝ) := by
              nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
            have h2 : 0 ≤ (2 - sqrt 3 : ℝ) := by nlinarith [Real.sqrt_nonneg 3]
            all_goals nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
          )
          ]
        rw [h11]
        have h12 : (2 - sqrt 3) * (2 + sqrt 3) = 1 := by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        rw [h12]
        simp
      nlinarith [h6, h7, h8, h9, h10, Real.sqrt_nonneg (2 - sqrt 3), Real.sqrt_nonneg (2 + sqrt 3), Real.sqrt_nonneg 6]
    have h10 : (sqrt 6) = (sqrt (2 - sqrt 3) + sqrt (2 + sqrt 3)) := by
      nlinarith [h3, Real.sqrt_nonneg (2 - sqrt 3), Real.sqrt_nonneg (2 + sqrt 3), Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (2 - sqrt 3 : ℝ) by
        have h1 : sqrt 3 ≤ (2 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
        have h2 : 0 ≤ (2 - sqrt 3 : ℝ) := by nlinarith [Real.sqrt_nonneg 3]
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      )
      ]
    linarith

  constructor
  · -- First part is $\sqrt{2} + \sqrt{2-\sqrt{3}} - \sqrt{2+\sqrt{3}} = 0$.
    linarith [h1]
  · -- Second part is $\sqrt{6} - \sqrt{2-\sqrt{3}} - \sqrt{2+\sqrt{3}} = 0$.
    linarith [h2]