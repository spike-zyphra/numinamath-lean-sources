import Mathlib

open Real

theorem algebra_278287 {a : ℝ} (ha : 1 < a) :
    min (min (min (sqrt (1993 * a) - sqrt (1993 * a - 1)) (sqrt (1993 * a - 1) - sqrt (1993 * a))) (sqrt (1993 * a) - sqrt (1993 * a + 1))) (sqrt (1993 * a + 1) - sqrt (1993 * a)) = sqrt (1993 * a - 1) - sqrt (1993 * a) := by

  have h1 : sqrt (1993 * a) - sqrt (1993 * a - 1) > 0 := by
    have h2 : sqrt (1993 * a) > sqrt (1993 * a - 1) := by
      apply Real.sqrt_lt_sqrt
      nlinarith
      nlinarith
    linarith [h2]

  have h3 : sqrt (1993 * a - 1) - sqrt (1993 * a) < 0 := by
    have h4 : sqrt (1993 * a) > sqrt (1993 * a - 1) := by
      apply Real.sqrt_lt_sqrt
      nlinarith
      nlinarith
    linarith [h4]

  have h4 : sqrt (1993 * a) - sqrt (1993 * a + 1) < 0 := by
    have h5 : sqrt (1993 * a + 1) > sqrt (1993 * a) := by
      apply Real.sqrt_lt_sqrt
      nlinarith
      nlinarith
    linarith [h5]

  have h5 : sqrt (1993 * a - 1) - sqrt (1993 * a) < sqrt (1993 * a) - sqrt (1993 * a + 1) := by
    have h6 : sqrt (1993 * a + 1) + sqrt (1993 * a - 1) < 2 * sqrt (1993 * a) := by
      nlinarith [Real.sqrt_nonneg (1993 * a + 1),
        Real.sqrt_nonneg (1993 * a - 1),
        Real.sqrt_nonneg (1993 * a),
        sq_nonneg (Real.sqrt (1993 * a + 1) - Real.sqrt (1993 * a)),
        sq_nonneg (Real.sqrt (1993 * a - 1) - Real.sqrt (1993 * a)),
        Real.sq_sqrt (show (0 : ℝ) ≤ 1993 * a + 1 by nlinarith),
        Real.sq_sqrt (show (0 : ℝ) ≤ 1993 * a - 1 by nlinarith),
        Real.sq_sqrt (show (0 : ℝ) ≤ 1993 * a by nlinarith),
        mul_nonneg (Real.sqrt_nonneg (1993 * a + 1)) (Real.sqrt_nonneg (1993 * a - 1)),
        sq_nonneg (Real.sqrt (1993 * a + 1) ^ 2 - Real.sqrt (1993 * a - 1) ^ 2 - 4)
      ]
    nlinarith [Real.sqrt_nonneg (1993 * a + 1),
      Real.sqrt_nonneg (1993 * a - 1),
      Real.sqrt_nonneg (1993 * a),
      h6
    ]

  have h7 : sqrt (1993 * a + 1) - sqrt (1993 * a) > 0 := by
    have h8 : sqrt (1993 * a + 1) > sqrt (1993 * a) := by
      apply Real.sqrt_lt_sqrt
      nlinarith
      nlinarith
    linarith [h8]

  have h6 : sqrt (1993 * a - 1) - sqrt (1993 * a) < sqrt (1993 * a + 1) - sqrt (1993 * a) := by
    nlinarith [h3, h7]

  have h8 : min (sqrt (1993 * a) - sqrt (1993 * a - 1)) (sqrt (1993 * a - 1) - sqrt (1993 * a)) = sqrt (1993 * a - 1) - sqrt (1993 * a) := by
    apply min_eq_right
    all_goals linarith [h1, h3]

  have h9 : min (min (sqrt (1993 * a) - sqrt (1993 * a - 1)) (sqrt (1993 * a - 1) - sqrt (1993 * a))) (sqrt (1993 * a) - sqrt (1993 * a + 1)) = sqrt (1993 * a - 1) - sqrt (1993 * a) := by
    rw [h8]
    apply min_eq_left
    all_goals linarith [h5]

  rw [h9]
  apply min_eq_left
  all_goals linarith [h6]