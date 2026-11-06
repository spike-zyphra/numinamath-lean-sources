import Mathlib

open Real

theorem algebra_112813 {x y : ℝ} (h : x^2 + y^2 - 8 * x * sqrt 3 - 6 * y * sqrt 2 + 66 = 0) :
    (⌊x⌋ - ⌊y⌋) / (⌊-x⌋ - ⌊-y⌋) < (1 + sqrt 2) / 2 := by

  have h1 : (x - 4 * sqrt 3) ^ 2 + (y - 3 * sqrt 2) ^ 2 = 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3),
      Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2),
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)),
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)),
      mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2)]

  have hx : x = 4 * sqrt 3 := by
    nlinarith [sq_nonneg (x - 4 * sqrt 3), sq_nonneg (y - 3 * sqrt 2)]

  have hy : y = 3 * sqrt 2 := by
    nlinarith [sq_nonneg (x - 4 * sqrt 3), sq_nonneg (y - 3 * sqrt 2)]

  have h2 : ⌊x⌋ = 6 := by
    rw [hx]
    have h3 : 6 ≤ (4 * Real.sqrt 3 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]
    have h4 : (4 * Real.sqrt 3 : ℝ) < (7 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> try nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h3, h4]
    <;> norm_num
    <;> nlinarith [h3, h4]

  have h3 : ⌊y⌋ = 4 := by
    rw [hy]
    have h4 : 4 ≤ (3 * Real.sqrt 2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2)]
    have h5 : (3 * Real.sqrt 2 : ℝ) < (5 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2)]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> try nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h4, h5]
    <;> norm_num
    <;> nlinarith [h4, h5]

  have h4 : ⌊-x⌋ = -7 := by
    rw [show -x = - (4 * Real.sqrt 3) by linarith [hx]]
    have h5 : -7 ≤ (- (4 * Real.sqrt 3) : ℝ) := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]
    have h6 : (- (4 * Real.sqrt 3) : ℝ) < (-6 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> try nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h5, h6]
    <;> norm_num
    <;> nlinarith [h5, h6]

  have h5 : ⌊-y⌋ = -5 := by
    rw [show -y = - (3 * Real.sqrt 2) by linarith [hy]]
    have h6 : -5 ≤ (- (3 * Real.sqrt 2) : ℝ) := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2)]
    have h7 : (- (3 * Real.sqrt 2) : ℝ) < (-4 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2)]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> try nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h6, h7]
    <;> norm_num
    <;> nlinarith [h6, h7]

  rw [h2, h3, h4, h5]
  have h6 : (Real.sqrt 2 : ℝ) > 0 := by positivity
  have h7 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
  norm_num at *
  nlinarith [Real.sqrt_nonneg 2, h7, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  all_goals linarith