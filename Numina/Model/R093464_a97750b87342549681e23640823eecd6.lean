import Mathlib

open Real

theorem inequalities_125893 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 1) :
    27 / 4 * (x + y) * (y + z) * (z + x) ≥
    (sqrt (x + y) + sqrt (y + z) + sqrt (z + x))^2 ∧
    (sqrt (x + y) + sqrt (y + z) + sqrt (z + x))^2 ≥ 6 * sqrt 3 := by

  have h1 : 27 / 4 * (x + y) * (y + z) * (z + x) ≥ (sqrt (x + y) + sqrt (y + z) + sqrt (z + x))^2 := by
    have h11 : sqrt (x + y) ≥ 0 := by positivity
    have h12 : sqrt (y + z) ≥ 0 := by positivity
    have h13 : sqrt (z + x) ≥ 0 := by positivity
    have h14 : (sqrt (x + y) + sqrt (y + z) + sqrt (z + x)) ^ 2 =
        (sqrt (x + y)) ^ 2 + (sqrt (y + z)) ^ 2 + (sqrt (z + x)) ^ 2 + 2 * (sqrt (x + y) * sqrt (y + z) + sqrt (y + z) * sqrt (z + x) + sqrt (z + x) * sqrt (x + y)) := by
      ring
    rw [h14]
    have h15 : (sqrt (x + y)) ^ 2 = x + y := Real.sq_sqrt (by linarith)
    have h16 : (sqrt (y + z)) ^ 2 = y + z := Real.sq_sqrt (by linarith)
    have h17 : (sqrt (z + x)) ^ 2 = z + x := Real.sq_sqrt (by linarith)
    rw [h15, h16, h17]
    nlinarith [sq_nonneg (sqrt (x + y) - sqrt (y + z)), sq_nonneg (sqrt (y + z) - sqrt (z + x)), sq_nonneg (sqrt (z + x) - sqrt (x + y)),
        Real.sq_sqrt (show 0 ≤ (x + y : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (y + z : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (z + x : ℝ) by linarith),
        Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x),
        mul_nonneg (Real.sqrt_nonneg (x + y)) (Real.sqrt_nonneg (y + z)), mul_nonneg (Real.sqrt_nonneg (y + z)) (Real.sqrt_nonneg (z + x)), mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (x + y)),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)
      ]
  have h2 : (sqrt (x + y) + sqrt (y + z) + sqrt (z + x))^2 ≥ 6 * sqrt 3 := by
    have h21 : sqrt (x + y) ≥ 0 := by positivity
    have h22 : sqrt (y + z) ≥ 0 := by positivity
    have h23 : sqrt (z + x) ≥ 0 := by positivity
    have h24 : (sqrt (x + y) + sqrt (y + z) + sqrt (z + x)) ^ 2 ≥ 6 * sqrt 3 := by
      have h14 : (sqrt (x + y) + sqrt (y + z) + sqrt (z + x)) ^ 2 =
          (sqrt (x + y)) ^ 2 + (sqrt (y + z)) ^ 2 + (sqrt (z + x)) ^ 2 + 2 * (sqrt (x + y) * sqrt (y + z) + sqrt (y + z) * sqrt (z + x) + sqrt (z + x) * sqrt (x + y)) := by
        ring
      rw [h14]
      have h15 : (sqrt (x + y)) ^ 2 = x + y := Real.sq_sqrt (by linarith)
      have h16 : (sqrt (y + z)) ^ 2 = y + z := Real.sq_sqrt (by linarith)
      have h17 : (sqrt (z + x)) ^ 2 = z + x := Real.sq_sqrt (by linarith)
      rw [h15, h16, h17]
      nlinarith [sq_nonneg (sqrt (x + y) - sqrt (y + z)), sq_nonneg (sqrt (y + z) - sqrt (z + x)), sq_nonneg (sqrt (z + x) - sqrt (x + y)),
          Real.sq_sqrt (show 0 ≤ (x + y : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (y + z : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (z + x : ℝ) by linarith),
          Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x),
          mul_nonneg (Real.sqrt_nonneg (x + y)) (Real.sqrt_nonneg (y + z)), mul_nonneg (Real.sqrt_nonneg (y + z)) (Real.sqrt_nonneg (z + x)), mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (x + y)),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith), Real.sqrt_nonneg (3 : ℝ),
          Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x)
          ]
    linarith
  constructor
  · exact h1
  · exact h2