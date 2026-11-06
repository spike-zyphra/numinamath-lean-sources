import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_1979 :
  IsLeast {t : ℝ | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 3 ∧ t = sqrt (2 * x + y) + sqrt (2 * y + z) + sqrt (2 * z + x)} (sqrt 6 + sqrt 3) := by
  constructor
  · -- Show that sqrt 6 + sqrt 3 is in the set.
    use 0, 3, 0
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · have h1 : sqrt (2 * (0 : ℝ) + (3 : ℝ)) = sqrt 3 := by
        norm_num
      have h2 : sqrt (2 * (3 : ℝ) + (0 : ℝ)) = sqrt 6 := by
        norm_num
      have h3 : sqrt (2 * (0 : ℝ) + (0 : ℝ)) = (0 : ℝ) := by
        simp
      rw [h1, h2, h3]
      all_goals
        ring
  · -- Show that sqrt 6 + sqrt 3 is the minimum.
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, hsum, ht⟩
    have h1 : sqrt (2 * x + y) + sqrt (2 * y + z) + sqrt (2 * z + x) ≥ sqrt 6 + sqrt 3 := by
      have h5 : 0 ≤ 2 * x + y := by nlinarith
      have h6 : 0 ≤ 2 * y + z := by nlinarith
      have h7 : 0 ≤ 2 * z + x := by nlinarith
      have h10 : (sqrt (2 * x + y)) ^ 2 = 2 * x + y := by
        rw [Real.sq_sqrt]
        nlinarith
      have h11 : (sqrt (2 * y + z)) ^ 2 = 2 * y + z := by
        rw [Real.sq_sqrt]
        nlinarith
      have h12 : (sqrt (2 * z + x)) ^ 2 = 2 * z + x := by
        rw [Real.sq_sqrt]
        nlinarith
      have h36 : (sqrt 6) ^ 2 = 6 := Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)
      have h37 : (sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
      have h38 : sqrt (2 * x + y) + sqrt (2 * y + z) + sqrt (2 * z + x) ≥ sqrt 6 + sqrt 3 := by
        have h39 : (sqrt (2 * x + y) + sqrt (2 * y + z) + sqrt (2 * z + x)) ^ 2 ≥ (sqrt 6 + sqrt 3) ^ 2 := by
          nlinarith [sq_nonneg (sqrt (2 * x + y) - sqrt 3), sq_nonneg (sqrt (2 * y + z) - sqrt 6), sq_nonneg (sqrt (2 * z + x) - 0),
            Real.sqrt_nonneg (2 * x + y), Real.sqrt_nonneg (2 * y + z), Real.sqrt_nonneg (2 * z + x),
            mul_nonneg (Real.sqrt_nonneg (2 * x + y)) (Real.sqrt_nonneg (2 * y + z)), 
            mul_nonneg (Real.sqrt_nonneg (2 * x + y)) (Real.sqrt_nonneg (2 * z + x)), 
            mul_nonneg (Real.sqrt_nonneg (2 * y + z)) (Real.sqrt_nonneg (2 * z + x)), 
            Real.sqrt_nonneg 6, Real.sqrt_nonneg 3, 
            mul_nonneg (Real.sqrt_nonneg 6) (Real.sqrt_nonneg 3)
          ]
        have h40 : (sqrt (2 * x + y) + sqrt (2 * y + z) + sqrt (2 * z + x)) ≥ 0 := by positivity
        have h41 : (sqrt 6 + sqrt 3) ≥ 0 := by positivity
        nlinarith [Real.sqrt_nonneg (2 * x + y), Real.sqrt_nonneg (2 * y + z), Real.sqrt_nonneg (2 * z + x), 
          Real.sqrt_nonneg 6, Real.sqrt_nonneg 3
        ]
      linarith
    have h2 : t = sqrt (2 * x + y) + sqrt (2 * y + z) + sqrt (2 * z + x) := by linarith [ht]
    nlinarith [Real.sqrt_nonneg (2 * x + y), Real.sqrt_nonneg (2 * y + z), Real.sqrt_nonneg (2 * z + x), 
      Real.sqrt_nonneg 6, Real.sqrt_nonneg 3
    ]