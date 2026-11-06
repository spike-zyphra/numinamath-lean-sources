import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_318063 (x y : ℝ) (hx : x ∈ Ioo (-sqrt 2) (sqrt 2)) (hy : y ∈ Ioo (-sqrt 2) (sqrt 2))
    (hxy : x * y = 1) :
    2 / (2 - x ^ 2) + 4 / (4 - y ^ 2) ≥ (16 + 4 * sqrt 2) / 7 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  have h1 : 0 < 2 - x^2 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h2 : 0 < 4 - y^2 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h3 : 0 < (2 - x^2) * (4 - y^2) := by
    positivity
  have h4 : 2 / (2 - x ^ 2) + 4 / (4 - y ^ 2) - (16 + 4 * sqrt 2) / 7 ≥ 0 := by
    have h5 : 2 / (2 - x ^ 2) + 4 / (4 - y ^ 2) - (16 + 4 * sqrt 2) / 7 =
        (7 * (2 * (4 - y^2) + 4 * (2 - x^2)) - (16 + 4 * sqrt 2) * ((2 - x^2) * (4 - y^2))) / (7 * (2 - x^2) * (4 - y^2)) := by
      field_simp
      <;> ring
    rw [h5] at *
    apply div_nonneg
    -- Prove numerator is non-negative.
    have h6 : x^2 * y^2 = 1 := by
      nlinarith [hxy, sq_nonneg (x * y)]
    nlinarith [sq_nonneg (x^2 - Real.sqrt 2 / 2), sq_nonneg (y^2 - Real.sqrt 2), 
      sq_nonneg (x^2 - Real.sqrt 2 / 2 - (y^2 - Real.sqrt 2)/2 ), 
      sq_nonneg (x^2 * y^2 - 1), 
      mul_pos (show 0 < 2 - x^2 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]) (show 0 < 4 - y^2 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)])
        , sq_nonneg (x^2 * y^2 - 1), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
            sq_nonneg (x^2 - y^2/(2:ℝ)), sq_nonneg (x * y * (x * y) -1), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) 
    ]
    all_goals
      positivity
  linarith