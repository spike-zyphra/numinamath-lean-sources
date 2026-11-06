import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_193861 (x : ℝ) :
  (3 - x ≥ 0 ∧ x + 1 ≥ 0 ∧ sqrt (3 - x) - sqrt (x + 1) > 1 / 2) ↔
  (-1 ≤ x ∧ x < 1 - sqrt 31 / 8) := by
  constructor
  · -- Assume the three conditions hold, prove $-1 \leq x$ and $x < 1 - \sqrt{31}/8$
    rintro ⟨h1, h2, h3⟩
    have h8 : sqrt (3 - x) ^ 2 > (sqrt (x + 1) + 1 / 2) ^ 2 := by
      have h4 : sqrt (3 - x) > sqrt (x + 1) + 1 / 2 := by linarith
      nlinarith [Real.sqrt_nonneg (3 - x), Real.sqrt_nonneg (x + 1)]
    have h10 : (sqrt (x + 1) + 1 / 2) ^ 2 = (x + 1) + sqrt (x + 1) + 1 / 4 := by
      nlinarith [Real.sqrt_nonneg (x + 1), Real.sq_sqrt (show 0 ≤ (x + 1 : ℝ) by linarith)]
    have h9 : sqrt (3 - x) ^2 = 3 - x := by
      rw [Real.sq_sqrt]
      linarith
    have h11 : (3 - x) > (x + 1) + sqrt (x + 1) + 1 / 4 := by
      nlinarith [h8, h9, h10, Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (3 - x)]
    have h12 : 7 / 4 - 2 * x > sqrt (x + 1) := by
      nlinarith [h11, Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (3 - x), Real.sq_sqrt (show 0 ≤ (31 : ℝ) by norm_num), Real.sqrt_nonneg (31), Real.sq_sqrt (show 0 ≤ (x + 1 : ℝ) by linarith), h1]
    have h14 : sqrt (x + 1) ^ 2 = x + 1 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h13 : (7 / 4 - 2 * x) ^ 2 > sqrt (x + 1) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x + 1), h12, Real.sqrt_nonneg (3 - x)]
    have h15 : (x) < (1 - Real.sqrt 31 / 8) := by
      nlinarith [h13, h14, Real.sqrt_nonneg (31), Real.sq_sqrt (show 0 ≤ (31 : ℝ) by norm_num), Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (3 - x), sq_nonneg (x - (1 - Real.sqrt 31 / 8)), sq_nonneg (sqrt (x + 1) - (1 / 2 : ℝ)), sq_nonneg (sqrt (3 - x) - sqrt (x + 1) - 1 / 2)]
    constructor
    · -- Show that -1 ≤ x
      nlinarith
    · -- Show that x < 1 - Real.sqrt 31 / 8
      linarith [h15]
  · -- Assume (-1 ≤ x ∧ x < 1 - sqrt 31 / 8) prove (3 - x ≥ 0 ∧ x + 1 ≥ 0 ∧ sqrt (3 - x) - sqrt (x + 1) > 1 / 2)
    rintro ⟨h1, h2⟩
    have h3 : x + 1 ≥ 0 := by nlinarith
    have h4 : 3 - x ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num), h2]
    constructor
    · -- Show 3 - x ≥ 0
      linarith
    constructor
    · -- Show x + 1 ≥ 0
      linarith
    · -- Show sqrt (3 - x) - sqrt (x + 1) > 1 / 2
      have h7 : (7 / 4 - 2 * x) > 0 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (31 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num)]
      have h8 : sqrt (3 - x) ^ 2 > (sqrt (x + 1) + 1 / 2) ^ 2 := by
        have h14 : sqrt (3 - x) ^ 2 = 3 - x := by
          rw [Real.sq_sqrt]
          nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num), h2]
        have h15 : (sqrt (x + 1) + 1 / 2) ^ 2 = (x + 1) + sqrt (x + 1) + 1 / 4 := by
          nlinarith [Real.sqrt_nonneg (x + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (x + 1 : ℝ) by nlinarith)]
        nlinarith [Real.sqrt_nonneg (3 - x), Real.sqrt_nonneg (x + 1), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 - x : ℝ) by nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num), h2]), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x + 1 : ℝ) by nlinarith), 
          sq_nonneg (sqrt (3 - x) - (sqrt (x + 1) + 1 / 2)), 
          sq_pos_of_pos (show 0 < (7 / 4 - 2 * x : ℝ) by 
            nlinarith [Real.sqrt_pos.mpr (show 0 < (31 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num)]
          ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num), 
          Real.sqrt_nonneg 31, 
          h7, 
          h1, 
          h2, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 - x : ℝ) by nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num), h2])
        ]
      have h17 : sqrt (3 - x) - sqrt (x + 1) > 1 / 2 := by
        by_contra h
        push_neg at h
        have h10 : sqrt (3 - x) ≤ sqrt (x + 1) + 1 / 2 := by linarith
        have h11 : sqrt (3 - x) ^ 2 ≤ (sqrt (x + 1) + 1 / 2) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (3 - x), Real.sqrt_nonneg (x + 1)]
        have h12 : (sqrt (3 - x) ^ 2) = 3 - x := by
          rw [Real.sq_sqrt]
          nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num), h2]
        have h13 : (sqrt (x + 1) + 1 / 2) ^ 2 = (x + 1) + sqrt (x + 1) + 1 / 4 := by
          nlinarith [Real.sqrt_nonneg (x + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (x + 1 : ℝ) by nlinarith)]
        nlinarith [Real.sqrt_nonneg (3 - x), Real.sqrt_nonneg (x + 1), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 - x : ℝ) by nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num), h2]), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x + 1 : ℝ) by nlinarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num), 
          Real.sqrt_nonneg 31, 
          h7, 
          h1, 
          h2, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 - x : ℝ) by nlinarith [Real.sqrt_nonneg 31, Real.sq_sqrt (show (0 : ℝ) ≤ (31 : ℝ) by norm_num), h2]
          )
        ]
      linarith