import Mathlib

theorem algebra_1210 {α : Type*} {I : Type*} {B : I → Set α} (A : Set α):
    A ∪ ⋂ i : I, B i = ⋂ i : I, (A ∪ B i) := by
  ext x 
  simp only [Set.mem_union, Set.mem_iInter]
  constructor
  · -- Assume x in left side, prove right side
    rintro (hA | hcap)
    · -- Case where x ∈ A
      intro i
      left
      exact hA
    · -- Case where x ∈ ⋂ i, B i
      intro i
      right
      exact hcap i 
  · -- Assume x in right side, prove left side
    intro h 
    have h1 : ∀ i : I, x ∈ A ∨ x ∈ B i := by 
      intro i
      have h2 := h i 
      simpa using h2 
    by_cases h2 : x ∈ A 
    · -- Case where x ∈ A
      left 
      exact h2
    · -- Case where x ∉ A 
      right 
      intro j 
      have h3 := h1 j 
      cases h3 with
      | inl h4 => 
        exfalso 
        have h3' : ¬ (x ∈ A) := h2
        contradiction 
      | inr h5 => 
        exact h5