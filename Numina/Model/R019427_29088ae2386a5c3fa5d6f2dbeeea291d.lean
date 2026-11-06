import Mathlib

open Real

theorem algebra_22037
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    (sqrt a + sqrt b + sqrt c) / sqrt (a + b + c) ≤ sqrt 3 ∧
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (sqrt a + sqrt b + sqrt c) / sqrt (a + b + c) = sqrt 3 := by

  have h1 : (sqrt a + sqrt b + sqrt c) ^ 2 ≤ 3 * (a + b + c) := by
    nlinarith [sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt b - sqrt c), sq_nonneg (sqrt c - sqrt a),
      Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (c : ℝ) by linarith),
      Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c,
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b),
      mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c),
      mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg a)
    ]
  
  have h2 : (sqrt a + sqrt b + sqrt c) / sqrt (a + b + c) ≤ sqrt 3 := by
    have h3 : (sqrt a + sqrt b + sqrt c) ^ 2 ≤ 3 * (a + b + c) := h1
    have h4 : (sqrt a + sqrt b + sqrt c) ≤ sqrt 3 * sqrt (a + b + c) := by
      have h5 : (sqrt a + sqrt b + sqrt c) ^ 2 ≤ 3 * (a + b + c) := h3
      have h6 : (sqrt 3 * sqrt (a + b + c)) ^ 2 ≥ (sqrt a + sqrt b + sqrt c) ^ 2 := by
        have h7 : (sqrt 3 * sqrt (a + b + c)) ^ 2 = (sqrt 3) ^ 2 * (sqrt (a + b + c)) ^ 2 := by ring
        have h8 : (sqrt 3) ^ 2 = (3 : ℝ) := by
          rw [Real.sq_sqrt]
          all_goals linarith
        have h9 : (sqrt (a + b + c)) ^ 2 = (a + b + c : ℝ) := by
          rw [Real.sq_sqrt]
          all_goals positivity
        rw [h7, h8, h9]
        nlinarith [sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt b - sqrt c), sq_nonneg (sqrt c - sqrt a), h3, Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c]
      have h10 : sqrt 3 * sqrt (a + b + c) ≥ 0 := by
        positivity
      have h11 : (sqrt a + sqrt b + sqrt c) ≥ 0 := by
        positivity
      nlinarith [sq_nonneg (sqrt 3 * sqrt (a + b + c) - (sqrt a + sqrt b + sqrt c)), sq_nonneg (sqrt 3 * sqrt (a + b + c)), sq_nonneg (sqrt a + sqrt b + sqrt c), h6, h10, h11, Real.sqrt_nonneg (a + b + c), Real.sqrt_nonneg 3, Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c
      ]
    have h6 : sqrt (a + b + c) > 0 := by
      positivity
    have h7 : (sqrt a + sqrt b + sqrt c) / sqrt (a + b + c) ≤ sqrt 3 := by
      have h8 : sqrt (a + b + c) > 0 := h6
      apply (div_le_iff₀ h8).mpr
      nlinarith [h4, Real.sqrt_nonneg (a + b + c), Real.sqrt_nonneg 3, Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c]
    exact h7

  refine ⟨h2, ?_⟩
  use 1, 1, 1
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · -- Verify the equation
    have h8 : sqrt (1 : ℝ) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h9 : sqrt (1 + 1 + 1 : ℝ) = Real.sqrt 3 := by
      norm_num
      all_goals linarith
    rw [h9]
    have h10 : sqrt (1 : ℝ) = 1 := h8
    rw [h10]
    have h11 : (1 + 1 + 1 : ℝ) / Real.sqrt 3 = Real.sqrt 3 := by
      have h12 : Real.sqrt 3 > 0 := by
        positivity
      field_simp
      <;> nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)]
    linarith [h11]