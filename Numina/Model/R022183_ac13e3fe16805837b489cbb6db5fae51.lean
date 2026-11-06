import Mathlib

theorem algebra_253730 :
    (3 * Real.sqrt 11 - 10 < 0) ∧ (10 * Real.sqrt 26 - 51 < 0) ∧ (18 - 5 * Real.sqrt 13 < 0) := by

  have h1 : 3 * Real.sqrt 11 < 10 := by
    nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show 0 ≤ (11 : ℝ) by norm_num), 
      sq_nonneg (3 * Real.sqrt 11 - 10), sq_nonneg (Real.sqrt 11 - 10 / 3),
      Real.sqrt_nonneg 11
    ]

  have h2 : 10 * Real.sqrt 26 < 51 := by
    nlinarith [Real.sqrt_nonneg 26, Real.sq_sqrt (show 0 ≤ (26 : ℝ) by norm_num),
      sq_nonneg (10 * Real.sqrt 26 - 51), sq_nonneg (Real.sqrt 26 - 51 / 10),
      Real.sqrt_nonneg 26
    ]

  have h3 : 18 - 5 * Real.sqrt 13 < 0 := by
    have h3' : 5 * Real.sqrt 13 > 18 := by
      nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show 0 ≤ (13 : ℝ) by norm_num),
          sq_nonneg (5 * Real.sqrt 13 - 18), sq_nonneg (Real.sqrt 13 - 18 / 5),
          Real.sqrt_nonneg 13
        ]
    linarith
  
  constructor
  · linarith [h1]

  constructor
  · linarith [h2]

  · linarith [h3]