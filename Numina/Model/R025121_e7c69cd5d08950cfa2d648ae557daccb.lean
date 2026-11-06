import Mathlib

theorem algebra_160037 {n m : ℝ} (hn : n = Real.sqrt 5) (hm : m = 400 ^ ((1 : ℝ) / 4)) :
    ((2 - n) / (n - 1) + 4 * (m - 1) / (m - 2)) /
    (n ^ 2 * (m - 1) / (n - 1) + m ^ 2 * (2 - n) / (m - 2)) = Real.sqrt 5 / 5 := by
  have h1 : m = 2 * Real.sqrt 5 := by
    rw [hm]
    have h400 : (400 : ℝ) ^ ((1 : ℝ) / 4) = 2 * Real.sqrt 5 := by
      have h10 : (400 : ℝ) ^ ((1 : ℝ) / 4) = (16 * (25 : ℝ)) ^ ((1 : ℝ) / 4) := by
        norm_num
      rw [h10]
      have h400 : (16 * (25 : ℝ)) ^ ((1 : ℝ) / 4) = (16 : ℝ) ^ ((1 : ℝ) / 4) * (25 : ℝ) ^ ((1 : ℝ) / 4) := by
        rw [Real.mul_rpow]
        all_goals norm_num
      rw [h400]
      have h17 : (16 : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) := by
        have h10 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
        rw [h10]
        have h18 : ((2 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) = (2 : ℝ) := by
          rw [← Real.rpow_mul]
          norm_num
          all_goals
            norm_num
        linarith
      have h20 : (25 : ℝ) ^ ((1 : ℝ) / 4) = Real.sqrt 5 := by
        have h100 : (25 : ℝ) ^ ((1 : ℝ) / 4) = (5 : ℝ) ^ (1 / 2 : ℝ) := by
          have h1300 : (25 : ℝ) = (5 : ℝ) ^ (2 : ℝ) := by norm_num
          rw [h1300]
          have h150 : ((5 : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 4) = (5 : ℝ) ^ (2 * (1 / 4 : ℝ)) := by
            rw [← Real.rpow_mul]
            ring_nf
            all_goals
              norm_num
          have h170 : (2 * (1 / 4 : ℝ)) = (1 / 2 : ℝ) := by
            linarith
          rw [h150, h170]
        rw [h100]
        have h4002 : (5 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 5 := by
          have h12 : (5 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 5 := by
            rw [← Real.sqrt_eq_rpow]
            all_goals
              norm_num
          exact h12
        linarith
      rw [h17, h20]
      all_goals
        linarith
    linarith
  have h2 : m = 2 * n := by
    rw [h1, hn]
  have hx1 : n - 1 ≠ 0 := by
    rw [hn]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have hx2 : m - 2 ≠ 0 := by
    rw [h1]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h3 : (2 - n) / (n - 1) + 4 * (m - 1) / (m - 2) = 3 * n / (n - 1) := by
    rw [show m = 2 * n by linarith [h2]]
    field_simp [(show n - 1 ≠ 0 by exact hx1), (show 2 * n - 2 ≠ 0 by
      intro h
      apply hx1
      linarith
    )
    ]
    ring
  have h4 : n ^ 2 * (m - 1) / (n - 1) + m ^ 2 * (2 - n) / (m - 2) = 3 * n^2 / (n - 1) := by
    rw [show m = 2 * n by linarith [h2]]
    field_simp [(show n - 1 ≠ 0 by exact hx1), (show 2 * n - 2 ≠ 0 by
      intro h
      apply hx1
      linarith
    )
    ]
    ring
  rw [h3, h4]
  rw [hn]
  have h7 : Real.sqrt 5 ≠ 0 := by
    have hne : Real.sqrt 5 > 0 := by
      positivity
    linarith
  have hx3 : Real.sqrt 5 - 1 ≠ 0 := by
    have hne : Real.sqrt 5 > 1 := by
      have h10 : Real.sqrt 5 > Real.sqrt 1 := by
        apply Real.sqrt_lt_sqrt
        all_goals norm_num
      have h11 : Real.sqrt 1 = 1 := Real.sqrt_one
      linarith
    linarith
  field_simp [h7, hx3]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (0 : ℝ) < 5), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]