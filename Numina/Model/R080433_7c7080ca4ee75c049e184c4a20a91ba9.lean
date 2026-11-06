import Mathlib

theorem number_theory_45841 (s : Finset ℕ) (h₀ : s.card = 100) :
    ∃ x ∈ s, 100 ∣ x ∨ ∃ t : Finset ℕ, t ⊆ s ∧ ∑ x ∈ t, x ≡ 0 [ZMOD 100] := by 
  have h₁ : s.Nonempty := by 
    apply Finset.nonempty_iff_ne_empty.2 
    by_contra h 
    rw [h] at h₀ 
    simp at h₀ 
  rcases h₁ with ⟨x, hx⟩
  use x, hx
  right
  use ∅ 
  constructor
  · simp 
  · simp [Int.ModEq]
    <;> omega