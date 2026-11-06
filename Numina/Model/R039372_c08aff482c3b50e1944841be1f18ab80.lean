import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_98428 {f : ℝ → ℝ} (hf : f = λ x => (2 * x + 3) / (x + 2)) :
    ∃ m M, ∀ x ≥ 0, f x ≤ M ∧ f x ≥ m ∧ m ∈ range f ∧ M ∉ range f := by

  use (3 / 2), (2 : ℝ)
  intro x hx
  have hfx1 : f x = (2 * x + 3) / (x + 2) := by
    simp [hf]

  have h1 : f x ≤ (2 : ℝ) := by
    rw [hfx1]
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith

  have h2 : f x ≥ (3 / 2 : ℝ) := by
    rw [hfx1]
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith

  have h3 : (3 / 2 : ℝ) ∈ range f := by
    use (0 : ℝ)
    simp [hf]

  have h4 : (2 : ℝ) ∉ range f := by
    intro h
    rcases h with ⟨y, hy⟩
    rw [hf] at hy
    simp at hy

    by_cases h5 : y + 2 = 0
    · -- Case where y + 2 = 0
      rw [h5] at hy
      norm_num [h5] at hy
    · -- Case where y + 2 ≠ 0
      field_simp [h5] at hy
      all_goals nlinarith

  constructor
  · -- Show that f x ≤ 2
    linarith [h1]

  constructor
  · -- Show that f x ≥ 3/2
    linarith [h2]

  constructor
  · -- Show that 3/2 is in the range
    exact h3

  · -- Show that 2 is not in the range
    exact h4