import Mathlib

open Real Set

theorem inequalities_82725 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a^2 + b^2 = 4) :
    a * b / (a + b + 2) ≤ sqrt 2 - 1 ∧
    (a * b / (a + b + 2) = sqrt 2 - 1 ↔ a = b) := by
  have h1 : 0 < a + b + 2 := by
    nlinarith [sq_nonneg (a - b), h]

  have h2 : a * b ≤ (sqrt 2 - 1) * (a + b + 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - sqrt 2), sq_nonneg (b - sqrt 2),
      Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
      mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), 
      sq_nonneg (a + b - 2 * sqrt 2), Real.sqrt_nonneg 2]

  have h3 : a * b / (a + b + 2) ≤ sqrt 2 - 1 := by
    have h4 : 0 < a + b + 2 := h1
    apply (div_le_iff₀ h4).mpr
    nlinarith [h2]

  have h4 : a * b / (a + b + 2) = sqrt 2 - 1 ↔ a = b := by
    constructor
    · -- Assume a * b / (a + b + 2) = sqrt 2 - 1, prove a = b
      intro heq
      have h_eq : a * b = (sqrt 2 - 1) * (a + b + 2) := by
        have h5 : 0 < a + b + 2 := h1
        field_simp at heq ⊢
        nlinarith [heq, h1]

      have h5 : (a - b) ^ 2 = 0 := by
        nlinarith [ sq_nonneg (a - b), sq_nonneg (a - sqrt 2), sq_nonneg (b - sqrt 2), 
          Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), 
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2) ]

      have h5' : a - b = 0 := by
        rw [sq_eq_zero_iff] at h5
        linarith

      linarith
    · -- Assume a = b, prove a * b / (a + b + 2) = sqrt 2 - 1
      intro heq
      have h_eq : a = b := heq
      have h_eq2 : 2 * a^2 = 4 := by
        have h_eq1 : b = a := by
          linarith [h_eq]
        rw [h_eq1] at h
        linarith
      have h_eq3 : a^2 = 2 := by
        linarith
      have h_eq4 : a = Real.sqrt 2 := by
        have h7 : a ≥ 0 := by linarith [ha]
        have h8 : a^2 = (2 : ℝ) := h_eq3
        have : a = Real.sqrt 2 := by
          rw [←h8]
          field_simp
        exact_mod_cast this
      have h_eq5 : b = Real.sqrt 2 := by
        nlinarith [h_eq4, h_eq, mul_nonneg ha hb]
      have h_eq6 : a * b = 2 := by
        rw [h_eq4, h_eq5]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have h_eq7 : a + b + 2 = 2 * Real.sqrt 2 + 2 := by
        rw [h_eq4, h_eq5]
        linarith
      rw [h_eq6, h_eq7]
      field_simp [(show 2 * Real.sqrt 2 + 2 ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        )]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

  constructor
  · exact h3
  · exact h4