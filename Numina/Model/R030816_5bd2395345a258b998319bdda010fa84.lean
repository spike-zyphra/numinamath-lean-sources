import Mathlib

theorem algebra_7518 :
  ∃! f : ℝ → ℝ, (∀ x y, x ≤ y → f x ≤ f y) ∧ (∀ x, f (f x) = x) := by
  use fun x => x
  constructor
  · -- Show that the identity function satisfies the two required conditions.
    constructor
    · -- Show that x ≤ y implies f x ≤ f y
      intro x y hxy
      exact hxy
    · -- Show that f (f x) = x
      intro x
      simp
  · -- Show that the identity function is unique.
    intro g h
    rcases h with ⟨h1, h2⟩
    funext x
    have h3 : g (g x) = x := h2 x
    by_cases h4 : g x < x
    · -- Assume g(x) < x.
      have h5 : g (g x) ≤ g x := by
        have h6 : g x ≤ x := by linarith
        have h7 : g (g x) ≤ g x := by
          apply h1 
          linarith
        linarith
      have h6 : x ≤ g x := by 
        linarith [h3, h5]
      linarith
    by_cases h5 : g x > x
    · -- Assume g x > x.
      have h6 : g (g x) ≥ g x := by
        have h7 : g x ≥ x := by linarith
        have h8 : g (g x) ≥ g x := by
          apply h1
          linarith
        linarith
      have h7 : x ≥ g x := by 
        linarith [h3, h6]
      linarith
    · -- Case g(x) = x
      have h8 : g x ≥ x := by linarith [show ¬ (g x < x) by linarith, h4]
      have h9 : g x ≤ x := by linarith [show ¬ (g x > x) by linarith, h5]
      linarith