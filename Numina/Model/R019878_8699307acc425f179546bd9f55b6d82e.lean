import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_310448 {k : ℝ} (f : ℝ → ℝ)
  (hf : f = λ x => (x + k) / ((k + 1) * x^2 + (2 * k + 2) * x + 2 * k - 3)) :
  ∀ x, ∃ y, f x = y ↔ k ≤ -1 ∨ k > 4 := by

  intro x
  by_cases h : k ≤ -1 ∨ k > 4
  · -- Case where k ≤ -1 ∨ k > 4 holds
    use (x + k) / ((k + 1) * x^2 + (2 * k + 2) * x + 2 * k - 3)
    constructor
    · -- Assume f x = y, prove k ≤ -1 ∨ k > 4
      intro h_eq
      tauto
    · -- Assume k ≤ -1 ∨ k > 4, prove f x = y
      intro h_eq
      simp [hf] at *
      <;> try tauto
  · -- Case where ¬(k ≤ -1 ∨ k > 4) holds
    have h2 : ¬(k ≤ -1 ∨ k > 4) := by
      simpa using h

    by_cases hdenom : (k + 1) * x^2 + (2 * k + 2) * x + 2 * k - 3 = 0
    · -- Case where denominator is zero
      have hfx : f x = (0 : ℝ) := by
        rw [hf]
        simp [hdenom]
      use (1 : ℝ)
      constructor
      · -- Assume f x = 1, prove k ≤ -1 ∨ k > 4
        intro h_eq
        have eq1 : (f x) = (1 : ℝ) := by linarith [h_eq]
        have eq2 : (0 : ℝ) = (1 : ℝ) := by
          linarith [hfx, eq1]
        have eq3 : k ≤ -1 ∨ k > 4 := by
          nlinarith
        tauto
      · -- Assume k ≤ -1 ∨ k > 4, prove f x = 1
        intro h_eq
        exfalso
        tauto
    · -- Case where denominator is non-zero
      have hfx_eq : f x = (x + k) / ((k + 1) * x^2 + (2 * k + 2) * x + 2 * k - 3) := by
        rw [hf]
      have h3 : (k + 1) * x^2 + (2 * k + 2) * x + 2 * k - 3 ≠ 0 := by
        by_contra h_eq
        contradiction
      use (f x + 1)
      constructor
      · -- Assume f x = f x + 1, prove k ≤ -1 ∨ k > 4
        intro h_eq
        have eq1 : f x = f x + 1 := by
          linarith [h_eq]
        have eq2 : (0 : ℝ) = (1 : ℝ) := by 
          have eq3 : f x = f x + 1 := eq1
          have h4 : f x = (x + k) / ((k + 1) * x^2 + (2 * k + 2) * x + 2 * k - 3) := hfx_eq
          rw [h4] at eq3
          field_simp [h3] at eq3 ⊢
          <;> linarith
        -- From 0 = 1 derive a contradiction, which implies the goal k ≤ -1 ∨ k > 4
        exfalso
        linarith
      · -- Assume k ≤ -1 ∨ k > 4, prove f x = f x + 1
        intro h_eq
        exfalso
        tauto