import Mathlib

theorem inequalities_599629 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) :
    Real.sqrt 2 < Real.sqrt (a + 1 / 2) + Real.sqrt (b + 1 / 2) ∧
    Real.sqrt (a + 1 / 2) + Real.sqrt (b + 1 / 2) ≤ 2 := by

  have h1 : 0 < b := hb

  have h2 : Real.sqrt (a + 1 / 2) ≥ 0 := by positivity
  have h3 : Real.sqrt (b + 1 / 2) ≥ 0 := by positivity

  have h4 : (Real.sqrt (a + 1 / 2) + Real.sqrt (b + 1 / 2)) ^ 2 ≤ (2 : ℝ) ^ 2 := by
    have h5 : (Real.sqrt (a + 1 / 2) + Real.sqrt (b + 1 / 2)) ^ 2 =
        (Real.sqrt (a + 1 / 2)) ^ 2 + (Real.sqrt (b + 1 / 2)) ^ 2 + 2 * (Real.sqrt (a + 1 / 2) * Real.sqrt (b + 1 / 2)) := by ring
    have h6 : (Real.sqrt (a + 1 / 2)) ^ 2 = a + 1 / 2 := by
      rw [Real.sq_sqrt]
      linarith
    have h7 : (Real.sqrt (b + 1 / 2)) ^ 2 = b + 1 / 2 := by
      rw [Real.sq_sqrt]
      linarith
    have h8 : (Real.sqrt (a + 1 / 2)) ^ 2 + (Real.sqrt (b + 1 / 2)) ^ 2 = 2 := by
      rw [h6, h7]
      linarith [h]
    have h9 : Real.sqrt (a + 1 / 2) * Real.sqrt (b + 1 / 2) ≤ (1 : ℝ) := by
      nlinarith [sq_nonneg (Real.sqrt (a + 1 / 2) - Real.sqrt (b + 1 / 2)), 
        sq_nonneg (a - b), 
        Real.sqrt_nonneg (a + 1 / 2), 
        Real.sqrt_nonneg (b + 1 / 2), 
        Real.sq_sqrt (show (0 : ℝ) ≤ a + 1 / 2 by linarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ b + 1 / 2 by linarith), 
        mul_pos ha hb
      ]
    nlinarith [h5, h8, h9, sq_nonneg (Real.sqrt (a + 1 / 2) - Real.sqrt (b + 1 / 2))]

  have h10 : Real.sqrt (a + 1 / 2) + Real.sqrt (b + 1 / 2) ≤ (2 : ℝ) := by nlinarith [h4, Real.sqrt_nonneg (a + 1 / 2), Real.sqrt_nonneg (b + 1 / 2)]

  have h11 : Real.sqrt (a + 1 / 2) + Real.sqrt (b + 1 / 2) > Real.sqrt 2 := by
    have h12 : (Real.sqrt (a + 1 / 2) + Real.sqrt (b + 1 / 2)) ^ 2 > (2 : ℝ) := by
      have h5 : (Real.sqrt (a + 1 / 2) + Real.sqrt (b + 1 / 2)) ^ 2 =
          (Real.sqrt (a + 1 / 2)) ^ 2 + (Real.sqrt (b + 1 / 2)) ^ 2 + 2 * (Real.sqrt (a + 1 / 2) * Real.sqrt (b + 1 / 2)) := by ring
      have h6 : (Real.sqrt (a + 1 / 2)) ^ 2 = a + 1 / 2 := by
        rw [Real.sq_sqrt]
        linarith
      have h7 : (Real.sqrt (b + 1 / 2)) ^ 2 = b + 1 / 2 := by
        rw [Real.sq_sqrt]
        linarith
      have h8 : Real.sqrt (a + 1 / 2) * Real.sqrt (b + 1 / 2) > (0 : ℝ) := by
        apply mul_pos
        · -- Show that `Real.sqrt (a + 1 / 2) > 0`
          apply Real.sqrt_pos.mpr
          linarith
        · -- Show that `Real.sqrt (b + 1 / 2) > 0`
          apply Real.sqrt_pos.mpr
          linarith
      nlinarith [h8]
    have h18 : 0 ≤ Real.sqrt (a + 1 / 2) + Real.sqrt (b + 1 / 2) := by positivity
    have h19 : 0 ≤ Real.sqrt (2 : ℝ) := by positivity
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
      h12, Real.sqrt_nonneg (a + 1 / 2), Real.sqrt_nonneg (b + 1 / 2)
    ]
  constructor
  · -- Prove the lower bound
    linarith [h11]
  · -- Prove the upper bound
    linarith [h10]