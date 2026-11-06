import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_301736 (a : ℝ) (ha : |a| ≥ 1) :
    arctan (1 / a) ∈ Ico (-π / 4) 0 ∪ Ioc 0 (π / 4) := by 
  by_cases h : a ≥ 0
  · -- Case $a \geq 0$, so $a \geq 1$
    have h1 : a ≥ 1 := by 
      rw [abs_of_nonneg h] at ha
      linarith
    have h2 : (1 / a) ≤ (1 : ℝ) := by 
      have h3 : a ≥ 1 := h1
      have h4 : a > 0 := by linarith
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith
    have h3 : 0 < (1 / a) := by 
      have h1 : a ≥ 1 := h1
      have h7 : a > 0 := by linarith
      positivity
    -- From $0 < 1/a \leq 1$, we know that $0 < \arctan(1/a) \leq \pi/4$.
    have h4 : arctan (1 / a) > 0 := by
      have h9 : 1 / a > 0 := h3
      -- arctan is strictly increasing and arctan 0 = 0, so arctan x > 0 for x > 0
      have ht1 : arctan (1 / a) > arctan (0 : ℝ) := by
        apply Real.arctan_strictMono
        linarith
      have ht2 : arctan (0 : ℝ) = 0 := by 
        rw [arctan_zero]
      linarith
    have h5 : arctan (1 / a) ≤ π / 4 := by 
      have h2 : 1 / a ≤ 1 := h2
      have h6 : arctan (1 / a) ≤ arctan (1 : ℝ) := by
        apply Real.arctan_le_arctan
        linarith
      have h7 : arctan (1 : ℝ) = π / 4 := by
        rw [arctan_one]
      linarith
    right
    constructor
    · -- Show arctan(1/a) > 0
      linarith
    · -- Show arctan(1/a) ≤ π / 4
      linarith
  · -- Case $a < 0$ 
    have h1 : a ≤ -1 := by
      rw [abs_of_neg (show a < 0 by linarith)] at ha
      linarith
    -- Show $-1 ≤ 1/a < 0$
    have h2 : -1 ≤ 1 / a := by
      have h1a : a ≤ -1 := h1
      have h2a : a < 0 := by nlinarith
      apply (le_div_iff_of_neg' (by linarith)).mpr
      nlinarith
    have h3 : 1 / a < 0 := by 
      have h1a : a ≤ -1 := h1
      have h2a : a < 0 := by nlinarith
      apply div_neg_of_pos_of_neg 
      all_goals linarith
    -- From $-1 ≤ 1/a < 0$, we know that $-\pi/4 ≤ \arctan(1/a) < 0$.
    have h4 : arctan (1 / a) ≥ -π / 4 := by 
      have h2 : -1 ≤ 1 / a := h2
      have h5 : arctan (1 / a) ≥ arctan (-1 : ℝ) := by
        apply Real.arctan_le_arctan
        linarith
      have h6 : arctan (-1 : ℝ) = -π / 4 := by 
        have h7 : arctan (-1 : ℝ) = - (arctan (1 : ℝ)) := by
          rw [arctan_neg]
          <;> simp
        have h8 : arctan (1 : ℝ) = π / 4 := by
          rw [arctan_one]
        nlinarith
      linarith
    have h5 : arctan (1 / a) < 0 := by 
      have h3 : 1 / a < 0 := h3
      have h6 : arctan (1 / a) < arctan (0 : ℝ) := by
        apply Real.arctan_lt_arctan
        linarith
      have h7 : arctan (0 : ℝ) = 0 := by 
        simp [arctan_zero]
      linarith
    left
    constructor
    · -- Show arctan(1/a) ≥ -π / 4
      linarith
    · -- Show arctan(1/a) < 0
      linarith