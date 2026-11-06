import Mathlib

theorem algebra_187732 : Real.sqrt (2 + Real.sqrt 3) = (Real.sqrt 2 * (Real.sqrt 3 + 1)) / 2 := by

  have h1 : (Real.sqrt 2 * (Real.sqrt 3 + 1)) / 2 ≥ 0 := by
    have h2 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
    have h3 : Real.sqrt 3 + 1 ≥ 0 := by
      have h4 : Real.sqrt 3 ≥ 0 := Real.sqrt_nonneg 3
      linarith
    have h5 : Real.sqrt 2 * (Real.sqrt 3 + 1) ≥ 0 := mul_nonneg h2 h3
    linarith
  have h2 : ( (Real.sqrt 2 * (Real.sqrt 3 + 1)) / 2 )^2 = 2 + Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 3 by norm_num), Real.sq_sqrt (show 0 ≤ 2 by norm_num),
      sq_nonneg (Real.sqrt 3 - 1), sq_nonneg (Real.sqrt 2 - 1)
    ]
  have h3 : Real.sqrt ( ( (Real.sqrt 2 * (Real.sqrt 3 + 1)) / 2 )^2 ) = (Real.sqrt 2 * (Real.sqrt 3 + 1)) / 2 := by
    rw [Real.sqrt_sq]
    all_goals
      linarith [h1]
  rw [show Real.sqrt (2 + Real.sqrt 3) = Real.sqrt ( ( (Real.sqrt 2 * (Real.sqrt 3 + 1)) / 2 )^2 ) by
    rw [h2]
  ]
  rw [h3]
  all_goals
    linarith