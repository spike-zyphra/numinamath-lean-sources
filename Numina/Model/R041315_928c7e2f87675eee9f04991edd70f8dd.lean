import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_14053 {f : ℝ → ℝ}
    (hf : ∀ x, f x = sqrt (x * (50 - x)) + sqrt (x * (2 - x))) :
    IsGreatest (image f (Icc 0 2)) 10 ∧
    IsMaxOn f (Icc 0 2) (25 / 13 : ℝ) := by 
  constructor
  · -- Show 10 is greatest in image
    constructor
    · -- Show 10 is in image
      use 25 / 13
      constructor
      · -- Show 25/13 in interval
        exact ⟨by norm_num, by norm_num⟩
      · -- Show that f(25/13) = 10
        rw [hf]
        have h1 : (25 / 13 : ℝ) * (50 - (25 / 13 : ℝ)) = (15625 / 169 : ℝ) := by norm_num
        have h2 : (25 / 13 : ℝ) * (2 - (25 / 13 : ℝ)) = (25 / 169 : ℝ) := by norm_num
        have h3 : sqrt ((25 / 13 : ℝ) * (50 - (25 / 13 : ℝ))) = (125 / 13 : ℝ) := by
          rw [h1]
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        have h4 : sqrt ((25 / 13 : ℝ) * (2 - (25 / 13 : ℝ))) = (5 / 13 : ℝ) := by
          rw [h2]
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h3, h4]
        norm_num
    · -- Show that 10 is greatest
      intro y hy
      rcases hy with ⟨x, hx, hfx⟩
      rw [hf] at hfx
      have hx1 : 0 ≤ x := by
        have h : x ∈ Icc (0 : ℝ) 2 := by
          simpa using hx
        exact h.1
      have hx2 : x ≤ (2 : ℝ) := by
        have h : x ∈ Icc (0 : ℝ) 2 := by
          simpa using hx
        exact h.2
      have h1 : 0 ≤ x * (50 - x) := by
        nlinarith
      have h2 : 0 ≤ x * (2 - x) := by
        nlinarith 
      have h3 : (sqrt (x * (50 - x)) + sqrt (x * (2 - x))) ^ 2 ≤ (10 : ℝ) ^ 2 := by 
        nlinarith [Real.sqrt_nonneg (x * (50 - x)), Real.sqrt_nonneg (x * (2 - x)), 
          Real.sq_sqrt (show 0 ≤ (x * (50 - x) : ℝ) by nlinarith), 
          Real.sq_sqrt (show 0 ≤ (x * (2 - x) : ℝ) by nlinarith), 
          mul_nonneg (Real.sqrt_nonneg (x * (50 - x))) (Real.sqrt_nonneg (x * (2 - x))), 
          sq_nonneg (x - 25 / 13)
        ]
      have h4 : sqrt (x * (50 - x)) + sqrt (x * (2 - x)) ≤ (10 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (x * (50 - x)), Real.sqrt_nonneg (x * (2 - x)), sq_nonneg (sqrt (x * (50 - x)) + sqrt (x * (2 - x)) - 10), h3
        ]
      nlinarith
  · -- Show IsMaxOn f (Icc 0 2) (25 / 13)
    unfold IsMaxOn
    intro x hx
    have hx1 : 0 ≤ x := by
      have h : x ∈ Icc (0 : ℝ) 2 := by
        simpa using hx
      exact h.1
    have hx2 : x ≤ (2 : ℝ) := by
      have h : x ∈ Icc (0 : ℝ) 2 := by
        simpa using hx
      exact h.2
    have h1 : 0 ≤ x * (50 - x) := by
      nlinarith 
    have h2 : 0 ≤ x * (2 - x) := by
      nlinarith 
    have h3 : f x ≤ 10 := by 
      rw [hf]
      have h3 : (sqrt (x * (50 - x)) + sqrt (x * (2 - x))) ^ 2 ≤ (10 : ℝ) ^ 2 := by 
        nlinarith [Real.sqrt_nonneg (x * (50 - x)), Real.sqrt_nonneg (x * (2 - x)), 
          Real.sq_sqrt (show 0 ≤ (x * (50 - x) : ℝ) by nlinarith), 
          Real.sq_sqrt (show 0 ≤ (x * (2 - x) : ℝ) by nlinarith), 
          mul_nonneg (Real.sqrt_nonneg (x * (50 - x))) (Real.sqrt_nonneg (x * (2 - x))), 
          sq_nonneg (x - 25 / 13)
          ]
      have h4 : sqrt (x * (50 - x)) + sqrt (x * (2 - x)) ≤ (10 : ℝ) := by 
        nlinarith [Real.sqrt_nonneg (x * (50 - x)), Real.sqrt_nonneg (x * (2 - x)), sq_nonneg (sqrt (x * (50 - x)) + sqrt (x * (2 - x)) - 10), h3 
          ]
      linarith
    have h4 : f (25 / 13 : ℝ) = 10 := by 
      rw [hf]
      have h1 : (25 / 13 : ℝ) * (50 - (25 / 13 : ℝ)) = (15625 / 169 : ℝ) := by norm_num 
      have h2 : (25 / 13 : ℝ) * (2 - (25 / 13 : ℝ)) = (25 / 169 : ℝ) := by norm_num 
      have h3 : sqrt ((25 / 13 : ℝ) * (50 - (25 / 13 : ℝ))) = (125 / 13 : ℝ) := by 
        rw [h1]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h4 : sqrt ((25 / 13 : ℝ) * (2 - (25 / 13 : ℝ))) = (5 / 13 : ℝ) := by 
        rw [h2]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      rw [h3, h4]
      norm_num
    have h5 : f x ≤ f (25 / 13 : ℝ) := by 
      linarith [h3, h4]
    exact h5