import Mathlib

theorem algebra_323957 {a : ℝ} (ha : a = Real.sqrt (Real.sqrt 2 + 1 / 8) / 2 - Real.sqrt 2 / 8) :
    a^2 + Real.sqrt (a^4 + a + 1) = Real.sqrt 2 := by 
  have h1 : a + Real.sqrt 2 / 8 = Real.sqrt (Real.sqrt 2 + 1 / 8) / 2 := by 
    rw [ha]
    all_goals ring
  have h2 : (a + Real.sqrt 2 / 8) ^ 2 = (Real.sqrt (Real.sqrt 2 + 1 / 8) / 2) ^ 2 := by 
    rw [h1]
  have h3 : (a + Real.sqrt 2 / 8) ^ 2 = (Real.sqrt (Real.sqrt 2 + 1 / 8)) ^ 2 / 4 := by 
    nlinarith [h2]
  have h4 : (Real.sqrt (Real.sqrt 2 + 1 / 8)) ^ 2 = Real.sqrt 2 + 1 / 8 := by 
    apply Real.sq_sqrt
    positivity
  have eq1 : (a + Real.sqrt 2 / 8) ^ 2 = (Real.sqrt 2 + 1 / 8) / 4 := by 
    rw [h3, h4]
    all_goals ring
  have eq2 : (a + Real.sqrt 2 / 8) ^ 2 = a^2 + Real.sqrt 2 / 4 * a + 1 / 32 := by
    have eq2a : (a + Real.sqrt 2 / 8) ^ 2 = a^2 + 2 * a * (Real.sqrt 2 / 8) + (Real.sqrt 2 / 8) ^ 2 := by
      ring
    rw [eq2a]
    have eq2b : 2 * a * (Real.sqrt 2 / 8) = (a * Real.sqrt 2) / 4 := by 
      ring_nf
    have eq2c : (Real.sqrt 2 / 8) ^ 2 = 1 / 32 := by 
      have h11 : Real.sqrt 2 ^ 2 = 2 := by
        exact Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)
      nlinarith [h11]
    rw [eq2b, eq2c]
    <;> ring_nf <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by positivity)]
  have eq3 : a^2 + Real.sqrt 2 / 4 * a - Real.sqrt 2 / 4 = 0 := by 
    nlinarith [eq1, eq2]
  have h5 : a ^ 2 = (Real.sqrt 2 / 4) * (1 - a) := by 
    nlinarith
  have h6 : a^4 + a + 1 = (Real.sqrt 2 - a^2) ^ 2 := by
    nlinarith [sq_nonneg (a ^ 2 - Real.sqrt 2 / 2), sq_nonneg (a + Real.sqrt 2 / 8), 
      Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (Real.sqrt 2 + 1 / 8 : ℝ), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by positivity), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (Real.sqrt 2 + 1 / 8 : ℝ) by positivity)
    ]
  have h7 : Real.sqrt (a^4 + a + 1) = Real.sqrt 2 - a^2 := by
    have h1 : Real.sqrt (a^4 + a + 1) = Real.sqrt ((Real.sqrt 2 - a^2) ^ 2) := by
      rw [h6]
    rw [h1]
    have h8 : Real.sqrt ((Real.sqrt 2 - a^2) ^ 2) = Real.sqrt 2 - a^2 := by
      rw [Real.sqrt_sq]
      nlinarith [sq_nonneg (a ^ 2 - Real.sqrt 2 / 2), sq_nonneg (a + Real.sqrt 2 / 8), 
        Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (Real.sqrt 2 + 1 / 8 : ℝ), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by positivity), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (Real.sqrt 2 + 1 / 8 : ℝ) by positivity)
      ]
    exact h8
  rw [h7]
  nlinarith [sq_nonneg (a ^ 2 - Real.sqrt 2 / 2), sq_nonneg (a + Real.sqrt 2 / 8), 
    Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (Real.sqrt 2 + 1 / 8 : ℝ), 
    Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by positivity), 
    Real.sq_sqrt (show (0 : ℝ) ≤ (Real.sqrt 2 + 1 / 8 : ℝ) by positivity)
  ]