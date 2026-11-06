import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_286531 {f : ℝ → ℝ} (hf : ∀ x, f x = x^2 + sqrt (1 - x^2)) :
    ∀ x, x ∈ Icc (-1) 1 → f x ∈ Icc 1 (5/4) := by
  intro x hx
  rw [mem_Icc] at hx
  have h1 : -1 ≤ x := hx.1
  have h2 : x ≤ 1 := hx.2
  have h3 : f x = x^2 + sqrt (1 - x^2) := hf x
  rw [h3]
  have h4 : 0 ≤ (1 - x^2 : ℝ) := by nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
  have h5 : 0 ≤ x^2 := by nlinarith
  have h6 : 1 ≤ (x^2 + sqrt (1 - x^2) : ℝ) := by
    nlinarith [sq_nonneg (x), sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (sqrt (1 - x^2) - 1 / 2), 
      Real.sqrt_nonneg (1 - x^2), 
      Real.sq_sqrt (show 0 ≤ (1 - x^2 : ℝ) by nlinarith), 
      Real.sq_sqrt (show 0 ≤ (1 - x^2 : ℝ) by nlinarith), 
      sq_nonneg (sqrt (1 - x^2) - 1 / 2), 
      Real.sq_sqrt (show 0 ≤ (1 - x^2 : ℝ) by nlinarith) 
    ]
  have h7 : (x^2 + sqrt (1 - x^2) : ℝ) ≤ (5 / 4 : ℝ) := by
    nlinarith [sq_nonneg (x), sq_nonneg (x ^ 2 - 3 / 4), sq_nonneg (sqrt (1 - x^2) - 1 / 2), 
      Real.sqrt_nonneg (1 - x^2), 
      Real.sq_sqrt (show 0 ≤ (1 - x^2 : ℝ) by nlinarith), 
      Real.sq_sqrt (show 0 ≤ (1 - x^2 : ℝ) by nlinarith), 
      sq_nonneg (sqrt (1 - x^2) - 1 / 2), 
      Real.sq_sqrt (show 0 ≤ (1 - x^2 : ℝ) by nlinarith) 
    ]
  constructor
  · -- Show that $1 \leq f(x)$
    linarith
  · -- Show that $f(x) \leq \frac{5}{4}$
    linarith
  all_goals try { nlinarith }