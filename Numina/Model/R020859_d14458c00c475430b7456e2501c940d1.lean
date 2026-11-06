import Mathlib

theorem number_theory_125061 (s : Finset ℕ) (h₀ : s.card = 11) :
    ∃ a b c d e f : ℕ,
      a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧ e ∈ s ∧ f ∈ s ∧
      (a^2 + b^2 + c^2) ≡ (d^2 + e^2 + f^2) [ZMOD 12] := by
  have h1 : s.Nonempty := by 
    apply Finset.nonempty_iff_ne_empty.mpr
    by_contra h
    rw [h] at h₀ 
    simp at h₀
  rcases h1 with ⟨x, hx⟩
  use x, x, x, x, x, x
  all_goals 
    simp [Int.ModEq] 
    <;> try { tauto } 
    <;> omega