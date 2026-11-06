import Mathlib

theorem inequalities_219881 (x : ℝ) (hx : x ∈ Set.Icc (3 / 2) 5) :
    2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x) < 2 * Real.sqrt 19 := by

  have h1 : 3 / 2 ≤ x := by
    have h2 : x ∈ Set.Icc (3 / 2) 5 := hx 
    simp at h2 ⊢ 
    linarith

  have h2 : x ≤ 5 := by
    have h3 : x ∈ Set.Icc (3 / 2) 5 := hx
    simp at h3 ⊢ 
    linarith

  have h3 : x + 1 ≥ 0 := by 
    linarith

  have h4 : 2 * x - 3 ≥ 0 := by
    linarith [show 3 / 2 ≤ x from h1]

  have h5 : 15 - 3 * x ≥ 0 := by
    linarith [show x ≤ 5 from h2]

  have h6 : (2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x)) ^ 2 < (2 * Real.sqrt 19) ^ 2 := by 
    have h7 : 0 ≤ (2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x)) := by 
      positivity 
    have h8 : 0 ≤ (2 * Real.sqrt 19) := by 
      positivity 
    have h14 : Real.sqrt (x + 1) ^ 2 = x + 1 := Real.sq_sqrt (by linarith) 
    have h15 : Real.sqrt (2 * x - 3) ^ 2 = 2 * x - 3 := Real.sq_sqrt (by linarith) 
    have h16 : Real.sqrt (15 - 3 * x) ^ 2 = 15 - 3 * x := Real.sq_sqrt (by linarith) 
    have h17 : Real.sqrt 19 ^ 2 = 19 := Real.sq_sqrt (show (0 : ℝ) ≤ 19 by norm_num)
    nlinarith [Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (2 * x - 3), 
      Real.sqrt_nonneg (15 - 3 * x), 
      sq_nonneg (Real.sqrt (x + 1) - Real.sqrt (2 * x - 3)), 
      sq_nonneg (Real.sqrt (x + 1) - Real.sqrt (15 - 3 * x)), 
      sq_nonneg (Real.sqrt (2 * x - 3) - Real.sqrt (15 - 3 * x)), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (x + 1 : ℝ) by linarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x - 3 : ℝ) by linarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (15 - 3 * x : ℝ) by linarith), 
      mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (2 * x - 3)), 
      mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (15 - 3 * x)), 
      mul_nonneg (Real.sqrt_nonneg (2 * x - 3)) (Real.sqrt_nonneg (15 - 3 * x))
    ]

  have h7 : 0 ≤ (2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x)) := by 
    positivity

  have h8 : 0 ≤ (2 * Real.sqrt 19) := by 
    positivity

  have h9 : (2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x)) < (2 * Real.sqrt 19) := by 
    nlinarith [h6, Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (2 * x - 3), 
      Real.sqrt_nonneg (15 - 3 * x), 
      Real.sqrt_nonneg 19, 
      mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (2 * x - 3)), 
      mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (15 - 3 * x)), 
      mul_nonneg (Real.sqrt_nonneg (2 * x - 3)) (Real.sqrt_nonneg (15 - 3 * x))
    ]

  exact h9