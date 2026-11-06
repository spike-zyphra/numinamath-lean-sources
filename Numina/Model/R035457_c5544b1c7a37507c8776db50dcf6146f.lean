import Mathlib


open Real


lemma lemma_1 {x : ℝ} (hx : x ≠ 0 ∧ x ≠ 2) :
    (2 * x / (x - 2) + (2 * x ^ 2 - 24) / x = 11 ↔ 2 * x ^ 3 - 13 * x ^ 2 - 2 * x + 48 = 0) := by
  constructor
  ·
    intro h
    have hx1 : x ≠ 0 := hx.1
    have hx2 : x ≠ 2 := hx.2
    have hx3 : x - 2 ≠ 0 := by
      intro h'
      apply hx2
      linarith
    field_simp [(show x - 2 ≠ 0 by assumption), (show x ≠ 0 by assumption)] at h ⊢
    nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by assumption), sq_pos_of_ne_zero (show (x - 2) ≠ 0 by assumption), sq_nonneg (x - 3), sq_nonneg (x + 2)]
  ·
    intro h
    have hx1 : x ≠ 0 := hx.1
    have hx2 : x ≠ 2 := hx.2
    have hx3 : x - 2 ≠ 0 := by
      intro h'
      apply hx2
      linarith
    field_simp [(show x - 2 ≠ 0 by assumption), (show x ≠ 0 by assumption)]
    nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by assumption), sq_pos_of_ne_zero (show (x - 2) ≠ 0 by assumption), sq_nonneg (x - 3), sq_nonneg (x + 2)]


theorem algebra_16378 :
  IsLeast {x : ℝ | x ≠ 2 ∧ x ≠ 0 ∧ 2 * x / (x - 2) + (2 * x ^ 2 - 24) / x = 11} ((1 - Real.sqrt 65) / 4) := by
  constructor
  · -- Verify that (1 - Real.sqrt 65) / 4 is in the set.
    constructor
    · -- Show $x \neq 2$.
      nlinarith [Real.sqrt_pos.mpr (show 0 < (65 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (65 : ℝ) by norm_num)]
    constructor
    · -- Show $x \neq 0$.
      nlinarith [Real.sqrt_pos.mpr (show 0 < (65 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (65 : ℝ) by norm_num)]
    · -- Show $2 * x / (x - 2) + (2 * x ^ 2 - 24) / x = 11$.
      have hx1 : ((1 - Real.sqrt 65) / 4 : ℝ) ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (65 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (65 : ℝ) by norm_num)]
      have hx2 : ((1 - Real.sqrt 65) / 4 : ℝ) ≠ 2 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (65 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (65 : ℝ) by norm_num)]
      have hx3 : ((1 - Real.sqrt 65) / 4 : ℝ) - 2 ≠ 0 := by
        intro h'
        apply hx2
        linarith
      have h2 : 2 * ((1 - Real.sqrt 65) / 4 : ℝ) ^ 3 - 13 * ((1 - Real.sqrt 65) / 4 : ℝ) ^ 2 - 2 * ((1 - Real.sqrt 65) / 4 : ℝ) + 48 = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (65 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (65 : ℝ) by norm_num), sq_pos_of_pos (show 0 < Real.sqrt 65 by positivity)
        ]
      apply (lemma_1 (And.intro hx1 hx2)).mpr
      nlinarith
  · -- Show that (1 - Real.sqrt 65) / 4 is the smallest element in the set.
    intro y hy
    rcases hy with ⟨hy1, hy2, hy3⟩
    have hx1 : y ≠ 0 := hy2
    have hx2 : y ≠ 2 := hy1
    have hx3 : y - 2 ≠ 0 := by
      intro h'
      apply hx2
      linarith
    have h1 : 2 * y ^ 3 - 13 * y ^ 2 - 2 * y + 48 = 0 := by
      have h2 : 2 * y / (y - 2) + (2 * y ^ 2 - 24) / y = 11 := hy3
      have h3 : 2 * y ^ 3 - 13 * y ^ 2 - 2 * y + 48 = 0 := by
        field_simp [(show y - 2 ≠ 0 by assumption), (show y ≠ 0 by assumption)] at h2 ⊢
        nlinarith [sq_pos_of_ne_zero (show y ≠ 0 by assumption), sq_pos_of_ne_zero (show (y - 2) ≠ 0 by assumption), sq_nonneg (y - 3), sq_nonneg (y + 2)
        ]
      linarith
    have h2 : (y - 6) * (2 * y ^ 2 - y - 8) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- First case, where the linear factor is zero
      have hy4 : y = 6 := by linarith
      nlinarith [Real.sqrt_pos.mpr (show 0 < (65 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (65 : ℝ) by norm_num)]
    · -- Second case, where the quadratic factor is zero
      have h5 : 2 * y ^ 2 - y - 8 = 0 := by linarith
      have h6 : (y - (1 + Real.sqrt 65) / 4) * (y - (1 - Real.sqrt 65) / 4) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (65 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (65 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h6) with h7 h8
      · -- First case, where the first factor is zero
        have hy4 : y = (1 + Real.sqrt 65) / 4 := by linarith
        nlinarith [Real.sqrt_pos.mpr (show 0 < (65 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (65 : ℝ) by norm_num)]
      · -- Second case, where the second factor is zero
        have hy4 : y = (1 - Real.sqrt 65) / 4 := by linarith
        nlinarith [Real.sqrt_pos.mpr (show 0 < (65 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (65 : ℝ) by norm_num)]