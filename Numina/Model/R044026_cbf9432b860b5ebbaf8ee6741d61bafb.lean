import Mathlib

open Real

theorem inequalities_601397 (x : ℝ) (hx : 3 / 2 ≤ x ∧ x ≤ 5) :
    2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x) < 2 * Real.sqrt 19 := by
  have h1 : 3 / 2 ≤ x := hx.1
  have h2 : x ≤ 5 := hx.2
  have h3 : x + 1 ≥ 0 := by nlinarith
  have h4 : 2 * x - 3 ≥ 0 := by nlinarith
  have h5 : 15 - 3 * x ≥ 0 := by nlinarith
  have h6 : Real.sqrt (x + 1) ≥ 0 := by positivity
  have h7 : Real.sqrt (2 * x - 3) ≥ 0 := by positivity
  have h8 : Real.sqrt (15 - 3 * x) ≥ 0 := by positivity
  have h9 : (2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x)) ^ 2 < 76 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x + 1 by nlinarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x - 3) by nlinarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ (15 - 3 * x) by nlinarith),
          mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (2 * x - 3)),
          mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (15 - 3 * x)),
          mul_nonneg (Real.sqrt_nonneg (2 * x - 3)) (Real.sqrt_nonneg (15 - 3 * x)),
          sq_nonneg (Real.sqrt (x + 1) - Real.sqrt (2 * x - 3)),
          sq_nonneg (Real.sqrt (x + 1) - Real.sqrt (15 - 3 * x)),
          sq_nonneg (Real.sqrt (2 * x - 3) - Real.sqrt (15 - 3 * x)),
          Real.sqrt_nonneg (19),
          Real.sq_sqrt (show (0 : ℝ) ≤ (19 : ℝ) by norm_num),
          sq_nonneg (x - (5 : ℝ)),
          sq_nonneg (x - (3 / 2 : ℝ))
        ]
  have h11 : Real.sqrt 76 = 2 * Real.sqrt 19 := by
    calc
      Real.sqrt 76 = Real.sqrt (4 * 19) := by norm_num
      _ = Real.sqrt 4 * Real.sqrt 19 := by rw [Real.sqrt_mul (by norm_num)]
      _ = (2 : ℝ) * Real.sqrt 19 := by
        have h2 : Real.sqrt 4 = (2 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h2]
  have h10 : (2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x)) < Real.sqrt 76 := by
    have h6 : (2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x)) ^ 2 < 76 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x + 1 by nlinarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x - 3) by nlinarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ (15 - 3 * x) by nlinarith),
          mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (2 * x - 3)),
          mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (15 - 3 * x)),
          mul_nonneg (Real.sqrt_nonneg (2 * x - 3)) (Real.sqrt_nonneg (15 - 3 * x)),
          sq_nonneg (Real.sqrt (x + 1) - Real.sqrt (2 * x - 3)),
          sq_nonneg (Real.sqrt (x + 1) - Real.sqrt (15 - 3 * x)),
          sq_nonneg (Real.sqrt (2 * x - 3) - Real.sqrt (15 - 3 * x)),
          Real.sqrt_nonneg (19),
          Real.sq_sqrt (show (0 : ℝ) ≤ (19 : ℝ) by norm_num),
          sq_nonneg (x - (5 : ℝ)),
          sq_nonneg (x - (3 / 2 : ℝ))
        ]
    have h3 : Real.sqrt 76 ≥ 0 := by positivity
    have h4 : Real.sqrt ((2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x)) ^ 2) = (2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x)) := by 
      rw [Real.sqrt_sq (by positivity)]
    have h5 : Real.sqrt 76 > (2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x)) := by
      have h6 : Real.sqrt ((2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x)) ^ 2) < Real.sqrt 76 := by
        apply Real.sqrt_lt_sqrt
        · positivity
        · nlinarith [h6, Real.sqrt_nonneg 76]
      have h7 : Real.sqrt ((2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x)) ^ 2) = (2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x)) := by
        rw [Real.sqrt_sq (by positivity)]
      nlinarith [h7, h6]
    nlinarith [Real.sqrt_nonneg 76, show Real.sqrt 76 > 0 by positivity, h5]
  nlinarith [h10, h11, Real.sqrt_nonneg 19]