import Mathlib

theorem algebra_6377 {f g : ℝ → ℝ} (hf1 : ∀ x y, f (x + g y) = y + g x) (hf2 : ∀ x y, g (f x + y) = y + g x) :
    (∀ x, f x = x) ∧ (∃ c, ∀ x, g x = x + c) := by

  have h1 : ∀ y, f (g y) = y + g 0 := by
    intro y
    specialize hf1 0 y
    norm_num at hf1 ⊢
    simpa using hf1

  have h2 : ∀ x, g (f x) = g x := by
    intro x
    specialize hf2 x 0
    norm_num at hf2 ⊢
    simpa using hf2

  have h3 : Function.Injective g := by
    intro a b hab
    have h4 : ∀ x, f (x + g a) = a + g x := by
      intro x
      specialize hf1 x a
      simpa using hf1
    have h5 : ∀ x, f (x + g b) = b + g x := by
      intro x
      specialize hf1 x b
      simpa using hf1
    have h7' : f (0 + g a) = a + g 0 := by
      simpa using h4 0
    have h8' : f (0 + g b) = b + g 0 := by
      simpa using h5 0
    have h9 : (0 + g a) = (0 + g b) := by
      linarith [hab]
    have h10 : f (0 + g a) = f (0 + g b) := by
      rw [h9]
    have h11 : a + g 0 = b + g 0 := by
      linarith [h7', h8', h10]
    linarith

  have h4 : ∀ x, f x = x := by
    intro x
    have h5 : g (f x) = g x := h2 x
    have h6 : f x = x := by
      apply h3
      all_goals linarith [h5]
    exact h6

  have h5 : ∃ c, ∀ x, g x = x + c := by
    use g 0
    intro x
    have eq1 := hf1 x 0
    simp [h4 (x + g 0), h4 x] at eq1 ⊢
    linarith

  constructor
  · -- Show that f(x) = x
    intro x
    apply h4 x
  · -- Show that there exists c, g(x) = x + c
    exact h5