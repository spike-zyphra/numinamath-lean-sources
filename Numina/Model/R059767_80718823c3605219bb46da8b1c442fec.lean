import Mathlib

open Set Real

theorem inequalities_144631 {f g : ℝ → ℝ}
    (hf : f = fun x => x ^ 2 - 2 * x)
    (hg : ∀ x, x ≥ 1 → g x = x - 2)
    (hg' : ∀ x, x < 1 → g x = -x) :
    {x | f x ≤ 3 * g x} = {x | -1 ≤ x ∧ x ≤ 0 ∨ 2 ≤ x ∧ x ≤ 3} := by
  ext x
  simp [hf]
  constructor
  · -- Assume f x ≤ 3 * g x, we need to prove -1 ≤ x ∧ x ≤ 0 ∨ 2 ≤ x ∧ x ≤ 3
    intro h
    by_cases h1 : x ≥ 1
    · -- x ≥ 1, so g x = x - 2
      have h2 : g x = x - 2 := hg x h1
      simp [h2] at h
      have h3 : 2 ≤ x := by nlinarith
      have h4 : x ≤ 3 := by nlinarith
      right
      exact ⟨h3, h4⟩
    · -- x < 1, so g x = -x
      have h2 : g x = -x := hg' x (lt_of_not_ge h1)
      simp [h2] at h
      have h3 : -1 ≤ x := by nlinarith
      have h4 : x ≤ 0 := by nlinarith
      left
      exact ⟨h3, h4⟩
  · -- Assume -1 ≤ x ∧ x ≤ 0 ∨ 2 ≤ x ∧ x ≤ 3, we need to prove f x ≤ 3 * g x
    rintro (h | h)
    · -- Case x ∈ [-1, 0]
      have h1 : x < 1 := by linarith
      have h2 : g x = -x := hg' x h1
      simp [h2]
      nlinarith
    · -- Case x ∈ [2, 3]
      have h1 : x ≥ 1 := by linarith
      have h2 : g x = x - 2 := hg x h1
      simp [h2]
      nlinarith