import Mathlib

theorem algebra_246092 (a b c : ℝ) (h₀ : a * b * c = 1) (h₁ : a + b + c > 1 / a + 1 / b + 1 / c) :
    (a > 1 ∧ b ≤ 1 ∧ c ≤ 1) ∨ (b > 1 ∧ a ≤ 1 ∧ c ≤ 1) ∨ (c > 1 ∧ a ≤ 1 ∧ b ≤ 1) := by

  have h2 : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 := by
    constructor
    · -- Show a ≠ 0 
      by_contra ha
      have h0' : a = 0 := by linarith [ha]
      rw [h0'] at h₀ 
      nlinarith 
    constructor
    · -- Show b ≠ 0 
      by_contra hb
      have h0' : b = 0 := by linarith [hb]
      rw [h0'] at h₀ 
      nlinarith 
    · -- Show c ≠ 0 
      by_contra hc
      have h0' : c = 0 := by linarith [hc]
      rw [h0'] at h₀ 
      nlinarith 
  have h3 : 1 / a = b * c := by 
    have ha : a ≠ 0 := h2.1 
    have hb : b ≠ 0 := h2.2.1 
    have hc : c ≠ 0 := h2.2.2 
    field_simp [ha, hb, hc] 
    <;> nlinarith
  have h4 : 1 / b = a * c := by 
    have ha : a ≠ 0 := h2.1 
    have hb : b ≠ 0 := h2.2.1 
    have hc : c ≠ 0 := h2.2.2 
    field_simp [ha, hb, hc] 
    <;> nlinarith 
  have h5 : 1 / c = a * b := by 
    have ha : a ≠ 0 := h2.1 
    have hb : b ≠ 0 := h2.2.1 
    have hc : c ≠ 0 := h2.2.2 
    field_simp [ha, hb, hc] 
    <;> nlinarith 
  have h6 : a + b + c > b * c + a * c + a * b := by 
    have h₁' : a + b + c > 1 / a + 1 / b + 1 / c := h₁
    rw [h3, h4, h5] at h₁' 
    linarith 
  by_cases h7 : a > 1 
  · -- Assume a > 1 
    by_cases h8 : b > 1 
    · -- Assume b > 1 
      by_cases h9 : c > 1 
      · -- Assume c > 1
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
                  mul_pos (show (0 : ℝ) < a - 1 by linarith) (show (0 : ℝ) < b - 1 by linarith), 
                  mul_pos (show (0 : ℝ) < a - 1 by linarith) (show (0 : ℝ) < c - 1 by linarith), 
                  mul_pos (show (0 : ℝ) < b - 1 by linarith) (show (0 : ℝ) < c - 1 by linarith), 
                  h₀ 
                ]
      · -- Assume c ≤ 1 
        exfalso 
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
                  mul_pos (show (0 : ℝ) < a - 1 by linarith) (show (0 : ℝ) < b - 1 by linarith), 
                  h₀ 
                ]
    · -- Assume b ≤ 1 
      have hb2 : b ≤ 1 := by linarith 
      by_cases h9 : c > 1 
      · -- Assume c > 1 
        exfalso 
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
                  mul_pos (show (0 : ℝ) < a - 1 by linarith) (show (0 : ℝ) < c - 1 by linarith), 
                  h₀ 
                ]
      · -- Assume c ≤ 1 
        have hc2 : c ≤ 1 := by linarith 
        left 
        constructor 
        · linarith 
        constructor 
        · linarith 
        · linarith 
  · -- Assume a ≤ 1 
    by_cases h8 : b > 1 
    · -- Assume b > 1 
      by_cases h9 : c > 1 
      · -- Assume c > 1 
        exfalso 
        nlinarith [sq_nonneg (b - 1), sq_nonneg (a - 1), sq_nonneg (c - 1), 
                  mul_pos (show (0 : ℝ) < b - 1 by linarith) (show (0 : ℝ) < c - 1 by linarith), 
                  h₀ 
                ]
      · -- Assume c ≤ 1 
        have hc2 : c ≤ 1 := by linarith 
        right 
        left 
        constructor 
        · linarith 
        constructor 
        · linarith 
        · linarith 
    · -- Assume b ≤ 1 
      have hb2 : b ≤ 1 := by linarith 
      by_cases h9 : c > 1 
      · -- Assume c > 1 
        right 
        right 
        constructor 
        · linarith 
        constructor 
        · linarith 
        · linarith 
      · -- Assume c ≤ 1 
        exfalso 
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
                  mul_nonneg (show (0 : ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ 1 - b by linarith), 
                  mul_nonneg (show (0 : ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ 1 - c by linarith), 
                  mul_nonneg (show (0 : ℝ) ≤ 1 - b by linarith) (show (0 : ℝ) ≤ 1 - c by linarith), 
                  h₀ 
                ]