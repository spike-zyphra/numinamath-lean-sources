import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_154452 (f : ℝ → ℝ → ℝ)
  (h₀ : ∀ a b, f a b = 3 / a + b)
  (M N : ℝ)
  (h₁ : ∃ a b, 1 ≤ a ∧ a ≤ b ∧ b ≤ 4 ∧ f a b = M)
  (h₂ : ∃ a b, 1 ≤ a ∧ a ≤ b ∧ b ≤ 4 ∧ f a b = N)
  (h₃ : ∀ a b, 1 ≤ a ∧ a ≤ b ∧ b ≤ 4 → f a b ≤ M) (h₄ : ∀ a b, 1 ≤ a ∧ a ≤ b ∧ b ≤ 4 → f a b ≥ N) :
  M - N = 7 - 2 * sqrt 3 := by
  have h1 : M ≥ 7 := by
    have h6 : f 1 4 = 7 := by
      rw [h₀]
      norm_num
    have h7 : f 1 4 ≤ M := h₃ 1 4 (by norm_num)
    linarith [h6, h7]
  have h2 : M ≤ 7 := by
    rcases h₁ with ⟨a, b, ha1, hab, hb4, heq⟩
    have h5 : f a b = 3 / a + b := h₀ a b
    rw [h5] at heq
    have h8 : f a b ≤ 7 := by
      rw [h₀]
      have h9 : 3 / a + b ≤ 7 := by
        have ha2 : 0 < a := by linarith
        have h10 : 3 / a + b ≤ 7 := by
          have h11 : 3 + a * b ≤ 7 * a := by
            nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 4), sq_nonneg (a - b),
                mul_nonneg (show 0 ≤ (a - 1 : ℝ) by nlinarith) (show 0 ≤ (b - a : ℝ) by nlinarith),
                mul_nonneg (show 0 ≤ (a - 1 : ℝ) by nlinarith) (show 0 ≤ (4 - b : ℝ) by nlinarith)
              ]
          have h12 : 3 / a + b = (3 + a * b) / a := by
            field_simp
            <;> ring
          rw [h12]
          apply (div_le_iff₀ (by linarith)).mpr
          linarith [h11]
        linarith [h10]
      linarith
    linarith [h8, heq, h₃ a b (show 1 ≤ a ∧ a ≤ b ∧ b ≤ 4 by tauto)]
  have h3 : N ≤ 2 * Real.sqrt 3 := by
    rcases h₂ with ⟨a, b, ha1, hab, hb4, heq⟩
    have h5 : f a b = 3 / a + b := h₀ a b
    rw [h5] at heq
    have h6 : f (Real.sqrt 3) (Real.sqrt 3) = 2 * Real.sqrt 3 := by
      rw [h₀]
      have h7 : Real.sqrt 3 > 0 := by positivity
      have h8 : 3 / Real.sqrt 3 = Real.sqrt 3 := by
        field_simp [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0)]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]
      rw [h8]
      all_goals linarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]
    have h7 : f (Real.sqrt 3) (Real.sqrt 3) ≥ N := h₄ (Real.sqrt 3) (Real.sqrt 3) (by
      constructor
      · -- Show that 1 ≤ Real.sqrt 3
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
      constructor
      · -- Show that Real.sqrt 3 ≤ Real.sqrt 3
        linarith
      · -- Show that Real.sqrt 3 ≤ 4
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
    )
    linarith [h6, h7]
  have h4 : N ≥ 2 * Real.sqrt 3 := by
    rcases h₂ with ⟨a, b, ha1, hab, hb4, heq⟩
    have h5 : f a b = 3 / a + b := h₀ a b
    rw [h5] at heq
    -- Show that 2 * sqrt(3) is a lower bound
    have h6 : f a b ≥ 2 * Real.sqrt 3 := by
      rw [h₀]
      have h7 : a > 0 := by linarith
      have h8 : Real.sqrt 3 > 0 := by positivity
      have h9 : 3 / a + b ≥ 2 * Real.sqrt 3 := by
        have h10 : a * b ≥ a * a := by nlinarith [show 0 ≤ a by linarith, show 0 ≤ b - a by linarith]
        have h11 : a * b ≥ a ^ 2 := by nlinarith
        have h12 : 3 / a + b ≥ 2 * Real.sqrt 3 := by
          have h13 : 3 / a + b - 2 * Real.sqrt 3 ≥ 0 := by
            have h14 : 3 / a + b - 2 * Real.sqrt 3 = (3 + a * b - 2 * a * Real.sqrt 3) / a := by
              field_simp
              <;> ring
            rw [h14]
            apply div_nonneg
            -- Show that numerator is non-negative
            nlinarith [sq_nonneg (a - Real.sqrt 3), sq_nonneg (b - Real.sqrt 3), sq_nonneg (a - 1), sq_nonneg (b - 4), sq_nonneg (a - b), 
              Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3), 
                mul_nonneg (show 0 ≤ (a - 1 : ℝ) by nlinarith) (show 0 ≤ (b - a : ℝ) by nlinarith), 
                mul_nonneg (show 0 ≤ (a - 1 : ℝ) by nlinarith) (show 0 ≤ (4 - b : ℝ) by nlinarith)
            ]
            linarith
          linarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]
        linarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]
      linarith
    have h7 : N ≤ f a b := by linarith [h₄ a b (show 1 ≤ a ∧ a ≤ b ∧ b ≤ 4 by tauto), heq]
    linarith [h7, h6]
  have h5 : M = 7 := by
    linarith [h1, h2]
  have h6 : N = 2 * Real.sqrt 3 := by
    linarith [h3, h4]
  rw [h5, h6]
  all_goals linarith