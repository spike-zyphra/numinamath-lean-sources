import Mathlib

theorem inequalities_265079 (a b c d : ℝ)
    (h₀ : a^2 + b^2 = 1) (h₁ : b^2 + c^2 = 1) (h₂ : c^2 + d^2 = 1) :
    a * b + a * c + a * d + b * c + b * d + c * d ≤ 3 ∧
    (a * b + a * c + a * d + b * c + b * d + c * d = 3 ↔
      (a = b ∧ b = c ∧ c = d)) := by
  constructor
  · -- First part: prove the inequality
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
              h₀, h₁, h₂, 
              sq_nonneg (a + c), sq_nonneg (b + d)]
  · -- Now prove the equality condition
    constructor
    · -- First direction: if equality holds, then variables are equal
      intro heq
      have h3 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
                  h₀, h₁, h₂, 
                  heq]
      have h4 : a - b = 0 := by
        rw [sq_eq_zero_iff] at h3
        linarith
      have h5 : a = b := by linarith
      -- Prove a = c
      have h3' : (a - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
                  h₀, h₁, h₂, 
                  heq]
      have h6 : a - c = 0 := by
        rw [sq_eq_zero_iff] at h3'
        linarith
      have h7 : a = c := by linarith
      -- Prove c = d
      have h3'' : (c - d) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
                  h₀, h₁, h₂, 
                  heq]
      have h8 : c - d = 0 := by
        rw [sq_eq_zero_iff] at h3''
        linarith
      have h9 : c = d := by linarith
      -- Prove a = b = c = d
      constructor
      · -- Show a = b
        linarith
      constructor
      · -- Show b = c
        linarith
      · -- Show c = d
        linarith
    · -- Second direction: if variables are equal, then equality holds
      rintro ⟨h₃, h₄, h₅⟩
      have h₆ : a = c := by
        linarith
      have h₇ : b = c := by
        linarith
      have h₈ : c = d := by
        linarith
      have h₉ : a^2 = 1 / 2 := by
        have h₆ : a^2 + b^2 = 1 := h₀
        have h7 : b = a := by
          linarith
        rw [h7] at h₆
        linarith
      -- Substitute all variables
      have h₇ : a * b + a * c + a * d + b * c + b * d + c * d = 6 * a^2 := by
        have h10 : b = a := by
          linarith
        have h11 : c = a := by
          linarith
        have h12 : d = a := by
          linarith
        rw [h10, h11, h12]
        all_goals ring
      -- Prove result
      rw [h₇]
      linarith [h₉]