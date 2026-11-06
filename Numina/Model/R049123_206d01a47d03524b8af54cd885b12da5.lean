import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_306163 (k : ℝ) :
  (∃ x : ℝ, 0 ≤ x ∧ x ≤ 2 ∧ sqrt x + sqrt (2 - x) ≥ k) ↔ k ≤ 2 := by 
  constructor
  · -- Assume there's a solution x, prove k ≤ 2
    intro h
    rcases h with ⟨x, hx1, hx2, hineq⟩
    -- For $x \in [0, 2]$, sqrt x + sqrt (2 - x) ≤ 2
    have h1 : sqrt x + sqrt (2 - x) ≤ 2 := by
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (2 - x), sq_nonneg (sqrt x - 1), sq_nonneg (sqrt (2 - x) - 1),
                  Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith [hx1]), Real.sq_sqrt (show (0 : ℝ) ≤ (2 - x) by linarith [hx2]), 
                  Real.sqrt_nonneg (x * (2 - x)), 
                  sq_nonneg (sqrt x - sqrt (2 - x)), 
                  mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (2 - x)), 
                  mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (x * (2 - x))), 
                  mul_nonneg (Real.sqrt_nonneg (2 - x)) (Real.sqrt_nonneg (x * (2 - x))), 
                  Real.sq_sqrt (show (0 : ℝ) ≤ x * (2 - x) by nlinarith)
                  ]
    linarith
  · -- Assume k ≤ 2, prove existence of x
    intro hk
    -- Choose x = 1 as discussed
    use 1
    constructor
    · -- Show 0 ≤ 1
      norm_num
    constructor
    · -- Show 1 ≤ 2
      norm_num
    · -- Show sqrt(1) + sqrt(1) ≥ k
      have h1 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      have h2 : sqrt (2 - (1 : ℝ)) = 1 := by
        have : (2 - (1 : ℝ) : ℝ) = (1 : ℝ) := by norm_num
        rw [this]
        exact Real.sqrt_one
      rw [h1, h2]
      -- Now need to show 2 ≥ k
      linarith
  all_goals norm_num