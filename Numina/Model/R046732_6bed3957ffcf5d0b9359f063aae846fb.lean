import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_259362 {f : ℝ → ℝ} (hf : f = λ x => 4^x - 3 * 2^x + 3)
  (hrange : range f = {y | 1 ≤ y ∧ y ≤ 7}) :
  ∀ x, 1 ≤ x ∧ x ≤ 2 ∨ x ≤ 0 := by

  have h1 : ∀ y, y ∈ range f ↔ 1 ≤ y ∧ y ≤ 7 := by
    intro y 
    rw [hrange]
    all_goals
      simp
  have h2 : (43 : ℝ) ∈ range f := by
    use (3 : ℝ)
    rw [hf]
    norm_num

  have h43 : (43 : ℝ) ∈ ( {y | 1 ≤ y ∧ y ≤ 7} : Set ℝ) := by
    have h4 : (43 : ℝ) ∈ range f := h2
    have h5 : (43 : ℝ) ∈ range f ↔ (1 ≤ (43 : ℝ) ∧ (43 : ℝ) ≤ 7) := h1 43
    have h6 : (1 ≤ (43 : ℝ) ∧ (43 : ℝ) ≤ 7) := by
      tauto
    simp at *
    tauto
  
  norm_num at h43
  all_goals
    intro x
    linarith