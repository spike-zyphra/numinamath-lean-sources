import Mathlib

open Real

theorem inequalities_87040 :
    (∃ n : ℕ, sqrt (9 - sqrt 77) * sqrt 2 * (sqrt 11 - sqrt 7) * (9 + sqrt 77) = n) ∧
    ∀ x y : ℝ, x * y = 6 → x > 2 → y > 2 → x + y < 5 := by
  constructor
  · -- Show that the number sqrt (9 - sqrt 77) * sqrt 2 * (sqrt 11 - sqrt 7) * (9 + sqrt 77) is natural
    use 8
    have h_eq : sqrt (9 - sqrt 77) * sqrt 2 * (sqrt 11 - sqrt 7) * (9 + sqrt 77) = (8 : ℝ) := by
      have h1 : (sqrt (9 - sqrt 77) * sqrt 2 * (sqrt 11 - sqrt 7) * (9 + sqrt 77)) ^ 2 = 64 := by
        calc
          (sqrt (9 - sqrt 77) * sqrt 2 * (sqrt 11 - sqrt 7) * (9 + sqrt 77)) ^ 2
            = (sqrt (9 - sqrt 77)) ^ 2 * (sqrt 2) ^ 2 * (sqrt 11 - sqrt 7) ^ 2 * (9 + sqrt 77) ^ 2 := by
              ring_nf
          _ = (9 - sqrt 77) * (2 : ℝ) * (18 - 2 * sqrt 77) * (9 + sqrt 77) ^ 2 := by
            have h4 : (sqrt (9 - sqrt 77)) ^ 2 = (9 - sqrt 77) := by
              rw [Real.sq_sqrt]
              nlinarith [Real.sqrt_nonneg (77 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 77 by norm_num)]
            have h5 : (sqrt 2) ^ 2 = (2 : ℝ) := by
              rw [Real.sq_sqrt]
              norm_num
            have h6 : (sqrt 11 - sqrt 7) ^ 2 = (18 - 2 * sqrt 77) := by
              have h7 : sqrt 77 = sqrt 7 * sqrt 11 := by
                rw [← Real.sqrt_mul (by norm_num)]
                all_goals norm_num
              nlinarith [Real.sqrt_nonneg (11 : ℝ), Real.sqrt_nonneg (7 : ℝ),
                  Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num),
                  Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num),
                  sq_nonneg (sqrt 11 - sqrt 7), Real.sqrt_nonneg (77 : ℝ), sq_nonneg (sqrt 11), sq_nonneg (sqrt 7),
                  mul_nonneg (Real.sqrt_nonneg (11 : ℝ)) (Real.sqrt_nonneg (7 : ℝ)),
                  Real.sq_sqrt (show (0 : ℝ) ≤ (77 : ℝ) by norm_num)
                ]
            have h7 : (9 + sqrt 77) ^ 2 = (9 + sqrt 77) ^ 2 := by
              ring
            rw [h4, h5, h6, h7]
            all_goals
              ring_nf
          _ = (64 : ℝ) := by
            nlinarith [Real.sqrt_nonneg (77 : ℝ), Real.sqrt_nonneg (11 : ℝ), Real.sqrt_nonneg (7 : ℝ),
                Real.sq_sqrt (show (0 : ℝ) ≤ (77 : ℝ) by norm_num),
                Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num),
                Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num),
                mul_nonneg (Real.sqrt_nonneg (11 : ℝ)) (Real.sqrt_nonneg (7 : ℝ)),
                Real.sqrt_nonneg (9 - sqrt 77 : ℝ)
              ]
      have h2 : sqrt (9 - sqrt 77) * sqrt 2 * (sqrt 11 - sqrt 7) * (9 + sqrt 77) ≥ 0 := by
        have h3 : sqrt (9 - sqrt 77) ≥ 0 := by positivity
        have h4 : sqrt 2 ≥ 0 := by positivity
        have h5 : sqrt 11 - sqrt 7 ≥ 0 := by
          have h6 : sqrt 11 ≥ sqrt 7 := Real.sqrt_le_sqrt (by norm_num)
          linarith [show sqrt 11 ≥ 0 by positivity, show sqrt 7 ≥ 0 by positivity]
        have h7 : (9 + sqrt 77) ≥ 0 := by positivity
        positivity
      have h3 : sqrt (9 - sqrt 77) * sqrt 2 * (sqrt 11 - sqrt 7) * (9 + sqrt 77) = 8 := by
        nlinarith [Real.sqrt_nonneg (9 - sqrt 77 : ℝ), Real.sqrt_nonneg (11 : ℝ), Real.sqrt_nonneg (7 : ℝ), Real.sqrt_nonneg (2 : ℝ),
          Real.sq_sqrt (show (0 : ℝ) ≤ (9 - sqrt 77 : ℝ) by nlinarith [Real.sqrt_nonneg (77 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (77 : ℝ) by norm_num)]
          ), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (77 : ℝ) by norm_num)
        ]
      linarith
    have h5 : sqrt (9 - sqrt 77) * sqrt 2 * (sqrt 11 - sqrt 7) * (9 + sqrt 77) = (8 : ℕ) := by
      norm_num at h_eq ⊢
      exact_mod_cast h_eq
    exact h5
  · -- Show that for any x, y with xy = 6 and x, y > 2, we have x + y < 5
    intro x y h1 h2 h3
    nlinarith [sq_pos_of_pos (sub_pos.mpr h2), sq_pos_of_pos (sub_pos.mpr h3), mul_pos (show 0 < x - 2 by linarith) (show 0 < y - 2 by linarith), sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (x - y), sq_nonneg (x * y - 6), h1
      ]