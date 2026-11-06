import Mathlib

theorem algebra_13086 : ∃ A B : ℕ, A > 0 ∧ B > 0 ∧ Real.sqrt (37 - Real.sqrt 1360) = Real.sqrt A - Real.sqrt B := by
  use 20, 17
  constructor
  · norm_num
  constructor
  · norm_num
  · -- We need to prove that $\sqrt{37 - \sqrt{1360}} = \sqrt{20} - \sqrt{17}$
    have h1 : Real.sqrt (37 - Real.sqrt 1360) = Real.sqrt (20 : ℝ) - Real.sqrt (17 : ℝ) := by
      have h2 : (Real.sqrt (20 : ℝ) - Real.sqrt (17 : ℝ)) ^ 2 = 37 - Real.sqrt 1360 := by
        have h3 : (Real.sqrt (20 : ℝ) - Real.sqrt (17 : ℝ)) ^ 2 = (Real.sqrt (20 : ℝ)) ^ 2 + (Real.sqrt (17 : ℝ)) ^ 2 - 2 * (Real.sqrt (20 : ℝ) * Real.sqrt (17 : ℝ)) := by
          ring
        rw [h3]
        have h4 : (Real.sqrt (20 : ℝ)) ^ 2 = (20 : ℝ) := Real.sq_sqrt (by norm_num)
        have h5 : (Real.sqrt (17 : ℝ)) ^ 2 = (17 : ℝ) := Real.sq_sqrt (by norm_num)
        have h6 : Real.sqrt (20 : ℝ) * Real.sqrt (17 : ℝ) = Real.sqrt (340 : ℝ) := by 
          rw [← Real.sqrt_mul (by norm_num)]
          norm_num
        rw [h4, h5, h6]
        have h7 : (Real.sqrt (340 : ℝ)) ^ 2 = (340 : ℝ) := Real.sq_sqrt (by norm_num)
        have h8 : (2 * Real.sqrt (340 : ℝ)) ^ 2 = (1360 : ℝ) := by 
          calc
            (2 * Real.sqrt (340 : ℝ)) ^ 2 = 4 * (Real.sqrt (340 : ℝ) ^ 2) := by ring
            _ = 4 * (340 : ℝ) := by 
              rw [h7]
            _ = (1360 : ℝ) := by norm_num
        have h9 : 2 * Real.sqrt (340 : ℝ) = Real.sqrt (1360 : ℝ) := by
          have h10 : (2 * Real.sqrt (340 : ℝ)) ^ 2 = (Real.sqrt (1360 : ℝ) ) ^ 2 := by 
            rw [h8]
            rw [Real.sq_sqrt]
            norm_num
          have h11 : 2 * Real.sqrt (340 : ℝ) ≥ 0 := by 
            positivity
          have h12 : Real.sqrt (1360 : ℝ) ≥ 0 := by 
            positivity
          nlinarith [Real.sqrt_nonneg (1360 : ℝ)]
        linarith [h9]
      have h11 : Real.sqrt (20 : ℝ) ≥ Real.sqrt (17 : ℝ) := by
        apply Real.sqrt_le_sqrt
        norm_num
      have h12 : Real.sqrt (20 : ℝ) - Real.sqrt (17 : ℝ) ≥ 0 := by
        linarith [h11]
      rw [← h2]
      have h4 : Real.sqrt ((Real.sqrt (20 : ℝ) - Real.sqrt (17 : ℝ)) ^ 2) = Real.sqrt (20 : ℝ) - Real.sqrt (17 : ℝ) := by 
        rw [Real.sqrt_sq (show 0 ≤ Real.sqrt (20 : ℝ) - Real.sqrt (17 : ℝ) by linarith [h12] ) ]
      rw [h4]
    norm_num at h1 ⊢
    linarith