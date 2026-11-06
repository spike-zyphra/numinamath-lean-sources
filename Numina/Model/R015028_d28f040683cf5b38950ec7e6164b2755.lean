import Mathlib

theorem algebra_258863 {f : ℝ → ℝ} (hf1 : f 1 = 1)
    (hfx : ∀ x, f (x + 5) ≥ f x + 5 ∧ f (x + 1) ≤ f x + 1) :
    (f 2002 + 1 - 2002) = 1 := by

  have h1 : ∀ x, f (x + 5) ≥ f x + 5 := by
    intro x
    exact (hfx x).1

  have h2 : ∀ x, f (x + 1) ≤ f x + 1 := by
    intro x
    exact (hfx x).2

  have h3 : ∀ x, f (x + 1) ≥ f x + 1 := by
    intro x
    have h4 : f (x + 5) ≥ f x + 5 := h1 x
    have h5 : f (x + 5) ≤ f (x + 4) + 1 := by
      specialize h2 (x + 4)
      rw [show (x + 4) + 1 = x + 5 by ring] at h2
      linarith
    have h6 : f (x + 4) ≤ f (x + 3) + 1 := by
      specialize h2 (x + 3)
      rw [show (x + 3) + 1 = x + 4 by ring] at h2
      linarith
    have h7 : f (x + 3) ≤ f (x + 2) + 1 := by
      specialize h2 (x + 2)
      rw [show (x + 2) + 1 = x + 3 by ring] at h2
      linarith
    have h8 : f (x + 2) ≤ f (x + 1) + 1 := by
      specialize h2 (x + 1)
      rw [show (x + 1) + 1 = x + 2 by ring] at h2
      linarith
    have h9 : f (x + 5) ≤ f (x + 1) + 4 := by
      linarith [h5, h6, h7, h8]
    linarith

  have h4 : ∀ x, f (x + 1) = f x + 1 := by
    intro x
    have h5 : f (x + 1) ≤ f x + 1 := h2 x
    have h6 : f (x + 1) ≥ f x + 1 := h3 x
    linarith

  have h5 : ∀ (n : ℕ), f (1 + (↑n : ℝ)) = 1 + (↑n : ℝ) := by
    intro n
    induction n with
    | zero =>
      norm_num
      all_goals linarith [hf1]
    | succ n ih =>
      have eq1 : (1 + ((↑(n + 1 : ℕ) : ℝ)) ) = (1 + ((↑n : ℝ)) ) + 1 := by
        simp at *
        all_goals linarith
      rw [eq1]
      have eq2 : f ((1 + ((↑n : ℝ)) ) + 1) = f (1 + ((↑n : ℝ)) ) + 1 := by
        specialize h4 (1 + ((↑n : ℝ)) )
        linarith
      rw [eq2, ih]
      all_goals
        simp at *
        all_goals linarith

  have h6 : f 2002 = 2002 := by
    specialize h5 2001
    norm_num at h5 ⊢
    linarith

  linarith [h6]