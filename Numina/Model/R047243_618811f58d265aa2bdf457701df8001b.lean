import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_311784 :
  IsLeast {z : ℝ | ∃ x y : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ x + y ≤ sqrt (2 / 3) ∧ z = sqrt (2 - 3 * x ^ 2) + sqrt (2 - 3 * y ^ 2)} (sqrt 2) := by 
  constructor
  · -- Show that sqrt 2 is in the set
    use 0
    use Real.sqrt (2 / 3)
    constructor
    · -- Show x ≥ 0
      norm_num
    constructor
    · -- Show y ≥ 0
      positivity
    constructor
    · -- Show x + y ≤ sqrt (2 / 3)
      have h2 : (0 : ℝ) + Real.sqrt (2 / 3) = Real.sqrt (2 / 3) := by ring
      rw [h2]
      all_goals try { linarith [Real.sqrt_nonneg (2 / 3), Real.sq_sqrt (show (0 : ℝ) ≤ (2 / 3 : ℝ) by norm_num) ] }
    · -- Verify z = sqrt (2 - 3 * x ^ 2) + sqrt (2 - 3 * y ^ 2)
      have h1 : Real.sqrt (2 / 3) ^ 2 = (2 / 3 : ℝ) := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      have h2 : Real.sqrt (2 - 3 * (Real.sqrt (2 / 3)) ^ 2) = (0 : ℝ) := by
        have h3 : (2 - 3 * (Real.sqrt (2 / 3)) ^ 2 : ℝ) = (0 : ℝ) := by
          nlinarith [h1]
        rw [h3]
        simp
      have h3 : Real.sqrt (2 - 3 * (0 : ℝ) ^ 2) = Real.sqrt 2 := by
        norm_num
      rw [h2, h3]
      all_goals ring_nf 
  · -- Show that sqrt 2 is the minimum
    intro z h
    rcases h with ⟨x, y, hx, hy, hxy, hz⟩
    have h1 : Real.sqrt 2 ≤ sqrt (2 - 3 * x ^ 2) + sqrt (2 - 3 * y ^ 2) := by
      have h2 : x^2 + y^2 ≤ (2 / 3 : ℝ) := by
        nlinarith [sq_nonneg (x + y - Real.sqrt (2 / 3)), 
          Real.sqrt_nonneg (2 / 3), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 / 3 : ℝ) by norm_num), 
          mul_nonneg hx hy, 
          sq_nonneg (x - y), 
          hxy
        ]
      have h3 : (sqrt (2 - 3 * x^2) + sqrt (2 - 3 * y^2)) ^ 2 ≥ (2 : ℝ) := by
        have h4 : (sqrt (2 - 3 * x^2) + sqrt (2 - 3 * y^2)) ^ 2 =
          (sqrt (2 - 3 * x^2))^2 + (sqrt (2 - 3 * y^2))^2 + 2 * (sqrt (2 - 3 * x^2) * sqrt (2 - 3 * y^2)) := by ring
        have h5 : (sqrt (2 - 3 * x^2))^2 = (2 - 3 * x^2) := Real.sq_sqrt (by nlinarith)
        have h6 : (sqrt (2 - 3 * y^2))^2 = (2 - 3 * y^2) := Real.sq_sqrt (by nlinarith)
        have h7 : sqrt (2 - 3 * x^2) * sqrt (2 - 3 * y^2) ≥ 0 := by positivity
        rw [h4, h5, h6]
        nlinarith [Real.sqrt_nonneg (2 - 3 * x^2), Real.sqrt_nonneg (2 - 3 * y^2), 
          sq_nonneg (sqrt (2 - 3 * x^2) - sqrt (2 - 3 * y^2)), 
          sq_nonneg (x^2 - y^2), 
          sq_nonneg (x - y), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 - 3 * x^2 : ℝ) by nlinarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 - 3 * y^2 : ℝ) by nlinarith), 
          mul_nonneg (Real.sqrt_nonneg (2 - 3 * x^2)) (Real.sqrt_nonneg (2 - 3 * y^2)), 
          mul_nonneg hx hy, 
          h2
        ]
      have h8 : sqrt (2) ≥ 0 := by positivity
      have h9 : sqrt (2 - 3 * x^2) + sqrt (2 - 3 * y^2) ≥ 0 := by positivity
      have h10 : sqrt (2) ≤ sqrt (2 - 3 * x^2) + sqrt (2 - 3 * y^2) := by
        nlinarith [Real.sqrt_nonneg (2 - 3 * x^2), Real.sqrt_nonneg (2 - 3 * y^2), 
          sq_nonneg (sqrt (2 - 3 * x^2) + sqrt (2 - 3 * y^2) - Real.sqrt 2), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 - 3 * x^2 : ℝ) by nlinarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 - 3 * y^2 : ℝ) by nlinarith), 
          h3, Real.sqrt_nonneg (2 : ℝ)
        ]
      exact h10
    nlinarith [h1, Real.sqrt_nonneg (2), Real.sqrt_nonneg (2 - 3 * x ^ 2), Real.sqrt_nonneg (2 - 3 * y ^ 2), hz]