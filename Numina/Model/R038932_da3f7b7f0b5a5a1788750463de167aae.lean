import Mathlib

theorem algebra_252486 {f : ℝ → ℝ} (h1 : ∀ x, f (10 + x) = f (10 - x)) (h2 : ∀ x, f (20 - x) = -f (20 + x)) :
    Odd f ∧ ∃ c, Function.Periodic f c := by
  have h3 : ∀ y, f y = f (20 - y) := by
    intro y
    have eq1 := h1 (y - 10)
    rw [show 10 + (y - 10 : ℝ) = y by ring] at eq1
    rw [show 10 - (y - 10 : ℝ) = (20 - y : ℝ) by ring] at eq1
    linarith

  have h4 : ∀ x, f (20 + x) = f (-x) := by
    intro x
    specialize h3 (20 + x)
    have eq1 : f (20 + x) = f (20 - (20 + x : ℝ)) := by
      simpa using h3
    have eq2 : f (20 - (20 + x : ℝ)) = f (-x) := by
      ring_nf at *
    linarith

  have h5 : ∀ x, f x = -f (-x) := by
    intro x
    have eq6 : f x = f (20 - x) := by
      specialize h3 x
      linarith
    have eq10 : f (20 - x) = -f (-x) := by
      have eq11 := h2 x
      have eq12 : f (20 + x) = f (-x) := h4 x
      linarith [eq11, eq12]
    linarith [eq6, eq10]

  -- Show that f is odd function.
  have h7 : Odd f := by
    use (fun x => (f x - 1) / 2)
    funext x
    have eq2 : f x = -f (-x) := h5 x
    field_simp at *
    <;> linarith [eq2]

  -- Show that f is periodic
  have h8 : ∃ c, Function.Periodic f c := by 
    use (0 : ℝ)
    all_goals
      unfold Function.Periodic
      intro x
      simp
  exact ⟨h7, h8⟩