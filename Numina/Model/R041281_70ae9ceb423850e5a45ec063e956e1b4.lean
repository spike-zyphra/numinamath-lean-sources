import Mathlib

theorem algebra_16396 (S : Finset (ℝ × ℝ)) (hS : S.card = 30)
    (hS1 : ∀ x y : ℝ, (x, y) ∈ S → ∃ a b : ℤ, a ∈ Set.Icc (-2) 2 ∧ b ∈ Set.Icc (-3) 3 ∧
      y = a * x + b) (hS2 : ∀ x y : ℝ, (x, y) ∈ S → ∀ x' y' : ℝ, (x', y') ∈ S →
    x ≠ x' ∨ y ≠ y') :
    {p | ∃ x y : ℝ, (x, y) ∈ S ∧ ∃ x' y' : ℝ, (x', y') ∈ S ∧ p = (x, y) ∧ p ≠ (x', y')}.ncard = 810 := by
  have h1 : S.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    by_contra h
    rw [h] at hS
    simp at hS
  rcases h1 with ⟨p, hp⟩
  rcases p with ⟨x, y⟩
  have h3 := hS2 x y hp x y hp
  cases h3 with
  | inl h4 =>
    have h5 : x ≠ x := h4
    exfalso
    exact h5 (by tauto)
  | inr h6 =>
    have h7 : y ≠ y := h6
    exfalso
    exact h7 (by tauto)