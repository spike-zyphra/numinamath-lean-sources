import Mathlib

def isSaturated (A : Set ℤ) : Prop := ∀ x ∈ A, ∃ y ∈ A, x + y ∈ A

def isFree (A : Set ℤ) : Prop := ∀ x ≠ 0, ∃ s : Finset ℤ, x = ∑ i ∈ s, i

theorem number_theory_318996 :
    ∃ A : Set ℤ, isSaturated A ∧ isFree A := by
  use {x | x ≠ 0}
  constructor
  · -- Show that {x | x ≠ 0} is Saturated
    intro x hx
    have h1 : x ≠ 0 := hx
    use x
    constructor
    · -- Show that x ∈ {x | x ≠ 0}
      simpa using h1
    · -- Show that x + x ∈ {x | x ≠ 0}
      have h2 : x + x ≠ 0 := by
        intro h
        have : x = 0 := by linarith
        contradiction
      simpa using h2
  · -- Show that {x | x ≠ 0} is Free
    intro x hx
    use {x}
    simp at hx ⊢
    all_goals linarith