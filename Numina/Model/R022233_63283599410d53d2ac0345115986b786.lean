import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_253958 (x : ℝ) :
  (2 - x) ≥ 0 ∧ x ≠ 0 ∧ (sqrt (2 - x) + 4 * x - 3) / x ≥ 2 ↔
  x < 0 ∨ x ∈ Icc 1 2 := by
  constructor
  · -- Assume (2 - x) ≥ 0 ∧ x ≠ 0 ∧ (sqrt (2 - x) + 4 * x - 3) / x ≥ 2, prove x < 0 ∨ x ∈ Icc 1 2
    rintro ⟨h1, hx, h2⟩
    by_cases h3 : x > 0
    · -- x > 0
      have h4 : sqrt (2 - x) + 4 * x - 3 ≥ 2 * x := by
        have h4 : (sqrt (2 - x) + 4 * x - 3) / x ≥ 2 := h2
        have hx' : x > 0 := h3
        have h5 : sqrt (2 - x) + 4 * x - 3 ≥ 2 * x := by
          have h6 : (sqrt (2 - x) + 4 * x - 3) / x - 2 ≥ 0 := by linarith
          have h7 : (sqrt (2 - x) + 4 * x - 3) / x - 2 = (sqrt (2 - x) + 4 * x - 3 - 2 * x) / x := by
            field_simp [hx]
            <;> ring
          rw [h7] at h6
          apply (le_div_iff₀ (by linarith)).mp at h6
          linarith
        linarith
      have h5 : 1 ≤ x := by
        by_contra h
        push_neg at h
        have h6 : x < 1 := h
        nlinarith [Real.sqrt_nonneg (2 - x), Real.sq_sqrt (show (2 - x : ℝ) ≥ 0 by linarith), sq_nonneg (sqrt (2 - x) - 1), sq_nonneg (x - 1), Real.sqrt_nonneg (2 - x)]
      right
      exact ⟨by linarith, by nlinarith⟩
    · -- x ≤ 0
      have h3' : x ≤ 0 := by nlinarith
      have h4 : x < 0 := by
        by_contra h
        push_neg at h
        have h5 : x = 0 := by nlinarith
        contradiction
      left
      linarith
  · -- Assume x < 0 ∨ x ∈ Icc 1 2, prove (2 - x) ≥ 0 ∧ x ≠ 0 ∧ (sqrt (2 - x) + 4 * x - 3) / x ≥ 2
    rintro (h | h)
    · -- x < 0
      have h1 : (2 - x : ℝ) ≥ 0 := by 
        nlinarith
      have h2 : x ≠ 0 := by 
        linarith
      have h3 : (sqrt (2 - x) + 4 * x - 3) / x ≥ 2 := by
        have h4' : sqrt (2 - x) + 4 * x - 3 ≤ x * 2 := by
          have h5 : sqrt (2 - x) + 2 * x - 3 ≤ 0 := by
            nlinarith [Real.sq_sqrt (show (2 - x : ℝ) ≥ 0 by linarith), Real.sqrt_nonneg (2 - x), sq_nonneg (sqrt (2 - x) - (3 - 4 * x)), sq_nonneg (x - (7 / 16)), Real.sqrt_nonneg (2 - x), mul_nonneg (show (0 : ℝ) ≤ 2 - x by nlinarith) (show (0 : ℝ) ≤ (2 - x) by nlinarith)]
          nlinarith [h5, Real.sqrt_nonneg (2 - x)]
        have h7 : (sqrt (2 - x) + 4 * x - 3) / x ≥ 2 := by
          apply (le_div_iff_of_neg' (by linarith)).mpr
          nlinarith [h4', Real.sqrt_nonneg (2 - x)]
        linarith
      exact ⟨h1, h2, h3⟩
    · -- x ∈ Icc 1 2
      rcases h with ⟨h1, h2⟩
      have h1 : 1 ≤ x := by linarith [h1]
      have h2 : x ≤ 2 := by linarith [h2]
      have h1' : (2 - x : ℝ) ≥ 0 := by 
        nlinarith
      have h2' : x ≠ 0 := by 
        nlinarith
      have h3 : (sqrt (2 - x) + 4 * x - 3) / x ≥ 2 := by
        apply (le_div_iff₀ (by linarith)).mpr
        have h4 : sqrt (2 - x) + 4 * x - 3 ≥ 2 * x := by
          nlinarith [Real.sqrt_nonneg (2 - x), Real.sq_sqrt (show (2 - x : ℝ) ≥ 0 by linarith), sq_nonneg (sqrt (2 - x) - 1), sq_nonneg (x - 1), Real.sqrt_nonneg (2 - x), Real.sq_sqrt (show (2 - x : ℝ) ≥ 0 by linarith), mul_nonneg (show (0 : ℝ) ≤ x - 1 by nlinarith) (show (0 : ℝ) ≤ 2 - x by nlinarith)]
        nlinarith
      exact ⟨h1', h2', h3⟩