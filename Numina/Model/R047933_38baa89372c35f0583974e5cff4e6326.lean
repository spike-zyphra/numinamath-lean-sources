import Mathlib

theorem other_24471 {x c : ℝ} (hx : x ≥ 1 / 2) (ha : c = Real.sqrt (x + Real.sqrt (2 * x - 1)) + Real.sqrt (x - Real.sqrt (2 * x - 1))) :
    (c = Real.sqrt 2 ↔ x ≤ 1) ∧ c ≠ 1 ∧ (c = 2 ↔ x = 3 / 2) := by

  have h1 : Real.sqrt (2 * x - 1) ≥ 0 := by 
    apply Real.sqrt_nonneg

  have h2 : x + Real.sqrt (2 * x - 1) ≥ 0 := by
    nlinarith [Real.sqrt_nonneg (2 * x - 1), Real.sq_sqrt (show (2 * x - 1 : ℝ) ≥ 0 by linarith)]

  have h3 : x - Real.sqrt (2 * x - 1) ≥ 0 := by
    nlinarith [Real.sqrt_nonneg (2 * x - 1), Real.sq_sqrt (show (2 * x - 1 : ℝ) ≥ 0 by linarith), sq_nonneg (Real.sqrt (2 * x - 1) - (x)), sq_nonneg (x - 1)]

  have hc2 : c ^ 2 = 2 * x + 2 * |x - 1| := by
    rw [ha]
    have h4 : Real.sqrt (x + Real.sqrt (2 * x - 1)) ^ 2 = x + Real.sqrt (2 * x - 1) := by 
      apply Real.sq_sqrt 
      nlinarith [Real.sqrt_nonneg (2 * x - 1), Real.sq_sqrt (show (2 * x - 1 : ℝ) ≥ 0 by linarith)]
    have h5 : Real.sqrt (x - Real.sqrt (2 * x - 1)) ^ 2 = x - Real.sqrt (2 * x - 1) := by 
      apply Real.sq_sqrt 
      nlinarith [Real.sqrt_nonneg (2 * x - 1), Real.sq_sqrt (show (2 * x - 1 : ℝ) ≥ 0 by linarith), sq_nonneg (Real.sqrt (2 * x - 1) - x), sq_nonneg (x - 1)]
    calc 
      (Real.sqrt (x + Real.sqrt (2 * x - 1)) + Real.sqrt (x - Real.sqrt (2 * x - 1))) ^ 2 
        = Real.sqrt (x + Real.sqrt (2 * x - 1)) ^ 2 + Real.sqrt (x - Real.sqrt (2 * x - 1)) ^ 2 + 2 * (Real.sqrt (x + Real.sqrt (2 * x - 1)) * Real.sqrt (x - Real.sqrt (2 * x - 1)) ) := by ring
      _ = (x + Real.sqrt (2 * x - 1)) + (x - Real.sqrt (2 * x - 1)) + 2 * (Real.sqrt (x + Real.sqrt (2 * x - 1)) * Real.sqrt (x - Real.sqrt (2 * x - 1)) ) := by rw [h4, h5]
      _ = 2 * x + 2 * (Real.sqrt (x + Real.sqrt (2 * x - 1)) * Real.sqrt (x - Real.sqrt (2 * x - 1)) ) := by ring
      _ = 2 * x + 2 * Real.sqrt ((x + Real.sqrt (2 * x - 1)) * (x - Real.sqrt (2 * x - 1))) := by 
        rw [Real.sqrt_mul (by 
          nlinarith [Real.sqrt_nonneg (2 * x - 1), Real.sq_sqrt (show (2 * x - 1 : ℝ) ≥ 0 by linarith)]
        )]
      _ = 2 * x + 2 * Real.sqrt (x ^ 2 - (Real.sqrt (2 * x - 1)) ^ 2) := by 
        rw [mul_sub]
        <;> ring
      _ = 2 * x + 2 * Real.sqrt (x ^ 2 - (2 * x - 1)) := by 
        rw [Real.sq_sqrt (show (2 * x - 1 : ℝ) ≥ 0 by linarith)]
      _ = 2 * x + 2 * Real.sqrt ((x - 1) ^ 2) := by 
        ring_nf
      _ = 2 * x + 2 * |x - 1| := by 
        rw [Real.sqrt_sq_eq_abs]

  -- Prove $c = \sqrt{2} \iff x \leq 1$
  have h4 : (c = Real.sqrt 2 ↔ x ≤ 1) := by 
    constructor
    · -- Assume c = Real.sqrt 2 prove x ≤ 1
      intro hc
      have hc2' : c ^ 2 = 2 := by 
        rw [hc]
        rw [Real.sq_sqrt (by norm_num)]
      rw [hc2] at hc2'
      by_cases h : x ≥ 1
      · -- x ≥ 1
        rw [abs_of_nonneg (by linarith)] at hc2'
        nlinarith
      · -- x < 1
        rw [abs_of_neg (by linarith)] at hc2'
        nlinarith
    · -- Assume x ≤ 1 prove c = Real.sqrt 2
      intro h
      have hc2' : c ^ 2 = 2 := by 
        rw [hc2]
        by_cases h' : x ≥ 1
        · -- x ≥ 1
          rw [abs_of_nonneg (by linarith)]
          nlinarith
        · -- x < 1
          rw [abs_of_neg (by linarith)]
          nlinarith
      have hc_pos : c ≥ 0 := by 
        rw [ha]
        positivity
      have h_pos : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
      nlinarith [hc2', Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 2]

  -- Prove $c \neq 1$
  have h5 : c ≠ 1 := by
    intro h_eq1
    have h_eq1' : c = 1 := by linarith
    have h_eq1'' : c ^ 2 = 1 := by 
      rw [h_eq1']
      norm_num
    rw [hc2] at h_eq1''
    by_cases h : x ≥ 1
    · -- x ≥ 1
      rw [abs_of_nonneg (by linarith)] at h_eq1''
      nlinarith
    · -- x < 1
      rw [abs_of_neg ( by linarith)] at h_eq1''
      nlinarith

  -- Prove $c = 2 \iff x = 3/2$
  have h6 : (c = 2 ↔ x = 3 / 2) := by
    constructor
    · -- Assume c = 2 prove x = 3/2
      intro hc2_eq2
      have hc2' : c ^ 2 = 4 := by 
        rw [hc2_eq2]
        norm_num
      rw [hc2] at hc2'
      by_cases h : x ≥ 1
      · -- x ≥ 1
        rw [abs_of_nonneg (by linarith)] at hc2'
        nlinarith
      · -- x < 1
        rw [abs_of_neg (by linarith)] at hc2'
        nlinarith
    · -- Assume x = 3/2 prove c = 2
      intro h
      have hc2_eq4 : c ^ 2 = 4 := by 
        rw [hc2]
        rw [h]
        norm_num [abs_of_nonneg]
      have hc_pos : c ≥ 0 := by 
        rw [ha]
        positivity
      nlinarith [hc2_eq4, Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]

  constructor
  · exact h4
  constructor
  · exact h5
  · exact h6