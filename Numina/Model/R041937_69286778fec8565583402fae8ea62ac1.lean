import Mathlib

theorem algebra_241720 (star : ℤ → ℤ → ℤ)
  (h₁ : ∀ x y : ℤ, star x (x + y) = y)
  (h₂ : ∀ x y : ℤ, star (x + y) y = x) :
  (∀ a b : ℤ, star a b = star b a) ∧
  (∃ a b c : ℤ, star (star a b) c ≠ star a (star b c)) :=
by

  -- Use h₁ with x and -x to show that star x 0 = -x
  have h3 : ∀ x : ℤ, star x 0 = -x := by
    intro x
    have h := h₁ x (-x)
    simp at h ⊢
    <;> linarith

  -- Use h₂ with y = 0 to show that star x 0 = x
  have h4 : ∀ x : ℤ, star x 0 = x := by
    intro x
    specialize h₂ x 0
    simp at h₂ ⊢
    <;> linarith

  -- So for all x, x = -x, which implies x = 0
  have h5 : ∀ x : ℤ, x = 0 := by
    intro x
    have h6 := h3 x
    have h7 := h4 x
    have h8 : x = 0 := by
      linarith
    exact h8

  -- Contradiction with 1 = 0
  have h8 : (1 : ℤ) = 0 := by
    apply h5 1

  linarith