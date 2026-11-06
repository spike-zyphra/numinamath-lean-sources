import Mathlib

theorem algebra_318863 {x : ℝ} (hx : x = 5 / (Real.sqrt 7 + Real.sqrt 2)) :
    Real.sqrt 2 = -1 / 10 * x^3 + 13 / 10 * x := by
  have h1 : Real.sqrt 7 ≥ 0 := Real.sqrt_nonneg 7
  have h2 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
  have h3 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by linarith)
  have h4 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by linarith)
  have hx5 : Real.sqrt 7 + Real.sqrt 2 ≠ 0 := by
    nlinarith [h1, h2, sq_pos_of_pos (show 0 < (7 : ℝ) by norm_num)
      , sq_pos_of_pos (show 0 < (2 : ℝ) by norm_num)
      , h3, h4, h3, h4
      ]
  have eq1 : x = 5 / (Real.sqrt 7 + Real.sqrt 2) := hx
  have eq4 : -1 / 10 * x^3 + 13 / 10 * x = Real.sqrt 2 := by
    rw [eq1]
    have hx5_pos : Real.sqrt 7 + Real.sqrt 2 > 0 := by
      nlinarith [Real.sqrt_nonneg 7, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_pos_of_pos (show (0 : ℝ) < (7 : ℝ) by norm_num), sq_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    have hx5_ne : Real.sqrt 7 + Real.sqrt 2 ≠ 0 := by
      nlinarith
    field_simp [hx5_ne]
    <;> nlinarith [sq_nonneg (Real.sqrt 7 - Real.sqrt 2), sq_nonneg (Real.sqrt 7 ^ 2 - 7), sq_nonneg (Real.sqrt 2 ^ 2 - 2), sq_nonneg ( (Real.sqrt 7 + Real.sqrt 2) ^ 2 - (9 + 2 * Real.sqrt 7 * Real.sqrt 2) ), sq_nonneg (Real.sqrt 7 * Real.sqrt 2), Real.sqrt_nonneg 7, Real.sqrt_nonneg 2, mul_nonneg (Real.sqrt_nonneg 7) (Real.sqrt_nonneg 2), sq_nonneg ( (Real.sqrt 7 + Real.sqrt 2) ^ 2 - 9 - 2 * Real.sqrt 7 * Real.sqrt 2 ), sq_nonneg ( (Real.sqrt 7 + Real.sqrt 2) ^ 2 - 9 - 2 * (Real.sqrt 7 * Real.sqrt 2) ), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 7 * Real.sqrt 2 - 2), sq_nonneg (Real.sqrt 7 ^ 2 - 7), sq_nonneg (Real.sqrt 2 ^ 2 - 2), sq_nonneg (Real.sqrt 7 + Real.sqrt 2)
    ]
  linarith [eq4]