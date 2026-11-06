import Mathlib
open Real

theorem number_theory_3755 : ⌊Real.sqrt 20 + Real.sqrt 18⌋ = 8 := by
  have h1 : Real.sqrt 20 ≥ 0 := by positivity
  have h2 : Real.sqrt 18 ≥ 0 := by positivity
  have h3 : 8 ≤ Real.sqrt 20 + Real.sqrt 18 := by
    nlinarith [Real.sqrt_nonneg 20, Real.sqrt_nonneg 18,
      Real.sq_sqrt (by norm_num : (20 : ℝ) ≥ 0),
      Real.sq_sqrt (by norm_num : (18 : ℝ) ≥ 0),
      mul_nonneg (Real.sqrt_nonneg 20) (Real.sqrt_nonneg 18),
      sq_nonneg (Real.sqrt 20 - Real.sqrt 18),
      sq_nonneg (Real.sqrt 20 + Real.sqrt 18 - 8),
      h1, h2,
      Real.sqrt_nonneg 20, Real.sqrt_nonneg 18,
      sq_nonneg (Real.sqrt 20 ^ 2 - Real.sqrt 18 ^ 2)
    ]
  have h4 : Real.sqrt 20 + Real.sqrt 18 < 9 := by
    nlinarith [Real.sqrt_nonneg 20, Real.sqrt_nonneg 18,
      Real.sq_sqrt (by norm_num : (20 : ℝ) ≥ 0),
      Real.sq_sqrt (by norm_num : (18 : ℝ) ≥ 0),
      mul_nonneg (Real.sqrt_nonneg 20) (Real.sqrt_nonneg 18),
      sq_nonneg (Real.sqrt 20 - Real.sqrt 18),
      sq_nonneg (Real.sqrt 20 + Real.sqrt 18 - 9),
      h1, h2,
      Real.sqrt_nonneg 20, Real.sqrt_nonneg 18,
      sq_nonneg (Real.sqrt 20 ^ 2 - Real.sqrt 18 ^ 2)
    ]
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> try linarith [h3, h4]