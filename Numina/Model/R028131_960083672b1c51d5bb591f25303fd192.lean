import Mathlib

open Real

theorem algebra_143391 {x y : ℝ} (hx : x = sqrt 33) (hy : y = sqrt 77) :
    ((x ^ 2 / y ^ 2 + y ^ 2 / x ^ 2 - 1) / (x ^ 3 / y ^ 3 + y ^ 3 / x ^ 3)) =
    sqrt 21 / 10 := by
  rw [hx, hy]
  have h1 : (sqrt 33 : ℝ) ^ 2 = 33 := by
    exact Real.sq_sqrt (by norm_num)
  have h2 : (sqrt 77 : ℝ) ^ 2 = 77 := by
    exact Real.sq_sqrt (by norm_num)
  have h3 : (sqrt 33 : ℝ) ^ 3 = (33 : ℝ) * (sqrt 33 : ℝ) := by
    calc
      (sqrt 33 : ℝ) ^ 3 = (sqrt 33 : ℝ) ^ 2 * (sqrt 33 : ℝ) := by ring
      _ = (33 : ℝ) * (sqrt 33 : ℝ) := by rw [h1]
  have h4 : (sqrt 77 : ℝ) ^ 3 = (77 : ℝ) * (sqrt 77 : ℝ) := by
    calc
      (sqrt 77 : ℝ) ^ 3 = (sqrt 77 : ℝ) ^ 2 * (sqrt 77 : ℝ) := by ring
      _ = (77 : ℝ) * (sqrt 77 : ℝ) := by rw [h2]
  have h9 : sqrt 33 > 0 := by
    positivity
  have h10 : sqrt 77 > 0 := by
    positivity
  have h11 : (sqrt 33 : ℝ) ≠ 0 := by linarith
  have h12 : (sqrt 77 : ℝ) ≠ 0 := by linarith
  rw [h3, h4]
  have h36 : sqrt 33 * sqrt 77 = sqrt 2541 := by
    have h37 : sqrt 33 * sqrt 77 = sqrt (33 * 77 : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]
    rw [h37]
    all_goals norm_num
  have h38 : sqrt 2541 = (11 : ℝ) * sqrt 21 := by
    have h39 : sqrt 2541 = sqrt (121 * 21 : ℝ) := by
      norm_num
    rw [h39]
    have h40 : sqrt ((121 * 21 : ℝ)) = sqrt (121 : ℝ) * sqrt (21 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num)]
    rw [h40]
    have h41 : sqrt (121 : ℝ) = (11 : ℝ) := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    rw [h41]
  field_simp [h1, h2, h11, h12, show sqrt 21 > 0 by positivity, show sqrt 21 ≠ 0 by positivity, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
  nlinarith [Real.sqrt_nonneg 21, Real.sqrt_nonneg 2541, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2541 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (77 : ℝ) by norm_num), Real.sqrt_nonneg 33, Real.sqrt_nonneg 77, mul_nonneg (Real.sqrt_nonneg 33) (Real.sqrt_nonneg 77)]