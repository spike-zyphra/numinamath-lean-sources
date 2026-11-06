import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_205575 (f : ℝ → ℝ → ℝ)
  (h₀ : ∀ a b, f a b = 3 / a + b)
  (M m : ℝ)
  (h₁ : ∃ a b, 1 ≤ a ∧ a ≤ b ∧ b ≤ 2 ∧ f a b = M)
  (h₂ : ∃ a b, 1 ≤ a ∧ a ≤ b ∧ b ≤ 2 ∧ f a b = m)
  (h₃ : ∀ a b, 1 ≤ a ∧ a ≤ b ∧ b ≤ 2 → f a b ≤ M) (h₄ : ∀ a b, 1 ≤ a ∧ a ≤ b ∧ b ≤ 2 → f a b ≥ m) :
  M - m = 5 - 2 * sqrt 3 := by

  have h1 : f 1 2 = 5 := by
    rw [h₀]
    norm_num

  have hM1 : M ≥ 5 := by
    have h12 : f 1 2 ≤ M := by
      apply h₃ 1 2
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    have h1 : f 1 2 = 5 := by
      rw [h₀]
      norm_num
    linarith [h1, h12]

  have hM2 : M ≤ 5 := by
    rcases h₁ with ⟨a, b, ha1, h9, hb2, hM_eq⟩
    have h7 : f a b ≤ 5 := by
      rw [h₀]
      have h1 : a ≥ 1 := by linarith
      have h2 : b ≤ 2 := by linarith
      have h3 : a ≤ b := by linarith
      have h4 : 3 / a + b ≤ 5 := by
        have h8 : 3 / a ≤ 3 := by
          have h9 : a ≥ 1 := by linarith
          have h10 : a > 0 := by linarith
          apply (div_le_iff₀ (by linarith)).mpr
          nlinarith
        have h11 : 3 + b ≤ 5 := by
          nlinarith
        have h10 : 3 / a + b ≤ 3 + b := by linarith
        nlinarith
      nlinarith
    linarith [hM1, h7, hM_eq]
  have hM_eq : M = 5 := by
    nlinarith

  have h12 : f (Real.sqrt 3) (Real.sqrt 3) = 2 * Real.sqrt 3 := by
    rw [h₀]
    have h2 : Real.sqrt 3 > 0 := by
      apply Real.sqrt_pos.mpr
      all_goals
        nlinarith
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)
    have h4 : 3 / (Real.sqrt 3) = Real.sqrt 3 := by
      field_simp [show Real.sqrt 3 ≠ 0 by nlinarith [Real.sqrt_nonneg 3]]
      all_goals
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by nlinarith)]
    nlinarith [h4, Real.sqrt_nonneg 3]

  have hm1 : m ≤ 2 * Real.sqrt 3 := by
    have hm2 : f (Real.sqrt 3) (Real.sqrt 3) ≥ m := by
      apply h₄ (Real.sqrt 3) (Real.sqrt 3)
      constructor
      · -- Show that 1 ≤ Real.sqrt 3
        have h10 : 1 < Real.sqrt 3 := Real.lt_sqrt_of_sq_lt (by norm_num : (1 : ℝ) ^ 2 < (3 : ℝ))
        nlinarith [Real.sqrt_nonneg 3]
      constructor
      · -- Show that Real.sqrt 3 ≤ Real.sqrt 3
        linarith
      · -- Show that Real.sqrt 3 ≤ 2
        have h14 : Real.sqrt 3 ≤ 2 := by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)]
        linarith
    have h16 : f (Real.sqrt 3) (Real.sqrt 3) = 2 * Real.sqrt 3 := h12
    linarith [h16, hm2]

  have hm2 : m ≥ 2 * Real.sqrt 3 := by
    rcases h₂ with ⟨a, b, ha1, h9, hb2, hm_eq⟩
    have h7 : f a b ≥ 2 * Real.sqrt 3 := by
      rw [h₀]
      have h10 : 1 ≤ a := by linarith
      have h11 : a ≤ b := by linarith
      have h12 : b ≤ 2 := by linarith
      have h14 : 3 / a + b ≥ 2 * Real.sqrt 3 := by
        have h20 : 0 < a := by nlinarith
        have h13 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)
        have h14 : 0 < Real.sqrt 3 := by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)]
        have h17 : 3 / a + b ≥ 2 * Real.sqrt 3 := by
          have h18 : (3 / a + b) - (2 * Real.sqrt 3) ≥ 0 := by
            have h19 : (3 / a + b) - (2 * Real.sqrt 3) = (3 + a * (b - 2 * Real.sqrt 3)) / a := by
              field_simp
              all_goals nlinarith
            rw [h19]
            have h12 : a > 0 := by nlinarith
            have h113 : 3 + a * (b - 2 * Real.sqrt 3) ≥ 0 := by
              nlinarith [sq_nonneg (a - Real.sqrt 3), sq_nonneg (b - Real.sqrt 3), 
                mul_nonneg (show (0 : ℝ) ≤ a - 1 by nlinarith) (show (0 : ℝ) ≤ b - a by nlinarith), 
                mul_nonneg (show (0 : ℝ) ≤ a - 1 by nlinarith) (show (0 : ℝ) ≤ 2 - b by nlinarith), 
                Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)]
            apply div_nonneg
            linarith
            linarith
          nlinarith
        linarith
      linarith
    linarith [hm_eq, h7]

  have hm_eq : m = 2 * Real.sqrt 3 := by
    linarith [hm1, hm2]

  rw [hM_eq, hm_eq]