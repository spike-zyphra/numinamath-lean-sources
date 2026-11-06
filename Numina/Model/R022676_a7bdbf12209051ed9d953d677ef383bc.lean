import Mathlib

theorem algebra_184287 {x : ℝ} (hx : x = Real.sqrt (3.92)) :
    ((1 + x + x^2) / (2 * x + x^2) + 2 - (1 - x + x^2) / (2 * x - x^2))^(-1 : ℤ) *
    (5 - 2 * x^2) = 0.04 := by

  have hx1 : x ^ 2 = 3.92 := by
    rw [hx]
    rw [Real.sq_sqrt]
    all_goals norm_num

  have hx2 : x ≠ 0 := by
    rw [hx]
    have h1 : Real.sqrt (3.92) > 0 := by
      positivity
    linarith

  have hx_ne_neg2 : x + 2 ≠ 0 := by
    by_contra h
    have : x = -2 := by linarith
    rw [this] at hx1
    norm_num at hx1

  have hx_ne_2 : x - 2 ≠ 0 := by
    by_contra h
    have : x = 2 := by linarith
    rw [this] at hx1
    norm_num at hx1

  have h1 : ((1 + x + x^2) / (2 * x + x^2) + 2 - (1 - x + x^2) / (2 * x - x^2))^(-1 : ℤ) *
    (5 - 2 * x^2) = 0.04 := by

    have h2 : 2 * x + x ^ 2 = x * (x + 2) := by ring
    have h4 : 2 * x - x ^ 2 = -x * (x - 2) := by ring

    rw [h2, h4]

    have h5 : ((1 + x + x ^ 2) / (x * (x + 2)) + 2 - ( (1 - x + x ^ 2) / (-x * (x - 2)) )) =
        (4 * x ^ 2 - 10) / ((x + 2) * (x - 2) ) := by
      field_simp [(show x ≠ 0 by assumption), show x + 2 ≠ 0 by
        intro h
        apply hx_ne_neg2
        linarith
      , show x - 2 ≠ 0 by
        intro h
        apply hx_ne_2
        linarith
      ]
      <;> nlinarith [hx1, sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (x ^ 2 - 4)]
    rw [h5]
    norm_num [zpow_neg_one, hx1]
    <;> field_simp [(show x + 2 ≠ 0 by
      intro h
      apply hx_ne_neg2
      linarith
    ), (show x - 2 ≠ 0 by
      intro h
      apply hx_ne_2
      linarith
    ), hx2
    ]
    <;> norm_num [hx1, sq_nonneg (x ^ 2 - 1)]
    all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3.92 by norm_num : (0 : ℝ) < 3.92), Real.sq_sqrt (show (0 : ℝ) ≤ (3.92 : ℝ) by norm_num : (0 : ℝ) ≤ 3.92)
    ]
    all_goals nlinarith
  exact h1