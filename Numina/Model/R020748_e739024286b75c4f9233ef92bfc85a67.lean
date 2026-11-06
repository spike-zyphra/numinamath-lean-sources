import Mathlib

open Real Set

theorem inequalities_2411 (x : ℝ) :
    0 ≤ 1 - x + x ^ 2 ∧ 0 ≤ 3 - x ^ 2 ∧ 0 ≤ 8 - 2 * x ∧ sqrt (1 - x + x ^ 2) +
    sqrt (3 - x ^ 2) ≤ sqrt (8 - 2 * x) ↔ -sqrt 3 ≤ x ∧ x ≤ sqrt 3 := by
  constructor
  · -- Prove the forward direction.
    intro h
    rcases h with ⟨h1, h2, h3, h4⟩
    have h5 : x ^ 2 ≤ 3 := by nlinarith
    have h6 : -sqrt 3 ≤ x := by
      have h7 : x ^ 2 ≤ 3 := h5
      have h8 : x ≥ -sqrt 3 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      linarith
    have h7 : x ≤ sqrt 3 := by
      have h8 : x ^ 2 ≤ 3 := h5
      have h9 : x ≤ sqrt 3 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      linarith
    constructor
    · linarith
    · linarith
  · -- Prove the backward direction.
    rintro ⟨h1, h2⟩
    have h3 : x ^ 2 ≤ 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (x ^ 2 - 3)]
    have h4 : 0 ≤ 1 - x + x ^ 2 := by
      nlinarith [sq_nonneg (x - 1 / 2)]
    have h5 : 0 ≤ 3 - x ^ 2 := by
      nlinarith [Real.sqrt_nonneg 3, h1, h2, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h6 : 0 ≤ 8 - 2 * x := by
      nlinarith [Real.sqrt_nonneg 3, h1, h2, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (x * (x * (x * (x))))]
    have h7 : sqrt (1 - x + x ^ 2) + sqrt (3 - x ^ 2) ≤ sqrt (8 - 2 * x) := by
      have h8 : (sqrt (1 - x + x ^ 2) + sqrt (3 - x ^ 2)) ^ 2 ≤ (sqrt (8 - 2 * x)) ^ 2 := by
        have h9 : (sqrt (1 - x + x ^ 2) + sqrt (3 - x ^ 2)) ^ 2 = (sqrt (1 - x + x ^ 2)) ^ 2 + (sqrt (3 - x ^ 2)) ^ 2 + 2 * (sqrt (1 - x + x ^ 2) * sqrt (3 - x ^ 2)) := by ring
        have h10 : (sqrt (1 - x + x ^ 2)) ^ 2 = 1 - x + x ^ 2 := by
          apply Real.sq_sqrt
          nlinarith
        have h11 : (sqrt (3 - x ^ 2)) ^ 2 = 3 - x ^ 2 := by
          apply Real.sq_sqrt
          nlinarith
        have h12 : (sqrt (8 - 2 * x)) ^ 2 = 8 - 2 * x := by
          apply Real.sq_sqrt
          nlinarith
        nlinarith [Real.sqrt_nonneg (1 - x + x ^ 2), Real.sqrt_nonneg (3 - x ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ (1 - x + x^2) by nlinarith
        ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 - x^2) by nlinarith
        ), sq_nonneg (sqrt (1 - x + x ^ 2) - sqrt (3 - x ^ 2)), sq_nonneg (x - 1 / 2), sq_nonneg (x ^ 2 - 1), sq_nonneg ((x) ^ 2 - 1), Real.sq_sqrt (show (0 : ℝ) ≤ (8 - 2 * x) by nlinarith
        )
        ]
      have h16 : sqrt (1 - x + x ^ 2) + sqrt (3 - x ^ 2) ≥ 0 := by positivity
      have h17 : sqrt (8 - 2 * x) ≥ 0 := by positivity
      nlinarith [Real.sqrt_nonneg (1 - x + x ^ 2), Real.sqrt_nonneg (3 - x ^ 2), Real.sqrt_nonneg (8 - 2 * x)]
    constructor
    · exact h4
    constructor
    · exact h5
    constructor
    · exact h6
    · exact h7