import Mathlib

theorem algebra_98008 : IsLeast {x : ℕ | x > (Real.sqrt 3 + Real.sqrt 2)^6} 970 := by

  have h1 : (Real.sqrt 3 + Real.sqrt 2) ^ 6 < (970 : ℝ) := by
    have h2 : (Real.sqrt 3 + Real.sqrt 2) ^ 6 = 485 + 198 * Real.sqrt 6 := by
      have h3 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
        calc
          Real.sqrt 6 = Real.sqrt (2 * 3) := by norm_num
          _ = Real.sqrt 2 * Real.sqrt 3 := by rw [Real.sqrt_mul (by norm_num)]
      have h4 : (Real.sqrt 3 + Real.sqrt 2) ^ 2 = 5 + 2 * Real.sqrt 6 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), h3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
      have h5 : (Real.sqrt 3 + Real.sqrt 2) ^ 6 = ((Real.sqrt 3 + Real.sqrt 2) ^ 2) ^ 3 := by ring
      rw [h5, h4]
      ring_nf
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 6]
    rw [h2]
    have h6 : Real.sqrt 6 < (2.45 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
      <;> nlinarith
    nlinarith [h6, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]

  have h3 : (969 : ℝ) < (Real.sqrt 3 + Real.sqrt 2) ^ 6 := by
    have h8 : (Real.sqrt 3 + Real.sqrt 2) ^ 6 = 485 + 198 * Real.sqrt 6 := by
      have h2 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
        calc
          Real.sqrt 6 = Real.sqrt (2 * 3) := by norm_num
          _ = Real.sqrt 2 * Real.sqrt 3 := by rw [Real.sqrt_mul (by norm_num)]
      have h4 : (Real.sqrt 3 + Real.sqrt 2) ^ 2 = 5 + 2 * Real.sqrt 6 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), h2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
      have h5 : (Real.sqrt 3 + Real.sqrt 2) ^ 6 = ((Real.sqrt 3 + Real.sqrt 2) ^ 2) ^ 3 := by ring
      rw [h5, h4]
      ring_nf
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 6]
    rw [h8]
    have h9 : (2.449 : ℝ) < Real.sqrt 6 := by
      rw [Real.lt_sqrt] <;> norm_num
      <;> nlinarith
    nlinarith [h9, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]

  constructor
  · -- Show 970 is in the set
    have h4 : (970 : ℕ) > (Real.sqrt 3 + Real.sqrt 2) ^ 6 := by
      have h5 : (Real.sqrt 3 + Real.sqrt 2) ^ 6 < (970 : ℝ) := h1
      norm_num at h5 ⊢
      exact_mod_cast h5
    exact h4
  · -- Show minimality
    intro x hx
    have h6 : x > (Real.sqrt 3 + Real.sqrt 2) ^ 6 := by
      exact hx
    by_contra h
    push_neg at h
    have h7 : x ≤ 969 := by
      omega
    have h8 : (x : ℝ) ≤ (969 : ℝ) := by
      norm_num at h7 ⊢
      exact_mod_cast h7
    have h9 : (Real.sqrt 3 + Real.sqrt 2) ^ 6 < (x : ℝ) := by
      linarith [h6, h3]
    linarith [h1, h3, h8, h9]