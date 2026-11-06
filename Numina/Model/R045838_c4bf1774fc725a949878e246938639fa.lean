import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_256539 {f g : ℝ → ℝ}
  (hf : f = λ x => x + 1 / x)
  (hg : ∀ x, ∃ y, g x = 2 * y - 1 ∧ f y = 2 * x - 1)
  (h : ∀ x, g x = x + 1 / x) :
  (∀ x, g x = x + 1 / x) ∧
  (∀ b, {x | g x = b}.encard = 1 → b = 9 / 2) ∧
  {x | logb 3 (g x) < logb 3 (9 / 2)} = {x | 9 / 2 < x ∧ x < 6} := by
  have h1 := hg 0
  rcases h1 with ⟨y, h2, h3⟩
  have h4 : g 0 = 0 + 1 / (0 : ℝ) := by
    specialize h 0
    simpa using h
  have h5 : g 0 = (0 : ℝ) := by
    rw [h4]
    norm_num
  have h6 : g 0 = 2 * y - 1 := h2
  have h7 : y = 1 / 2 := by
    linarith [h5, h6]
  have h8 : f y = 2 * (0 : ℝ) - 1 := by
    simpa using h3
  rw [hf] at h8
  simp at h8
  rw [h7] at h8
  norm_num at h8
  all_goals norm_num [h7] at h8 <;> linarith