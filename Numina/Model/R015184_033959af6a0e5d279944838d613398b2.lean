import Mathlib

theorem algebra_117719 (f : ℝ → ℝ) (g : ℝ → ℝ)
    (h₁ : ∀ x, f (x + 5) ≥ f x + 5) (h₂ : ∀ x, f (x + 1) ≤ f x + 1)
    (h₃ : g = fun x => f x + 1 - x) (h₄ : f 1 = 1) :
    g 2002 = 1 := by

  have h5 : ∀ x, f (x + 1) = f x + 1 := by
    intro x
    have h7 : f (x + 5) ≥ f x + 5 := h₁ x
    have h8 : f (x + 1) ≤ f x + 1 := h₂ x
    have h9 : f (x + 2) ≤ f (x + 1) + 1 := by
      specialize h₂ (x + 1)
      rw [show x + 1 + 1 = x + 2 by ring] at h₂
      linarith
    have h10 : f (x + 3) ≤ f (x + 2) + 1 := by
      specialize h₂ (x + 2)
      rw [show x + 2 + 1 = x + 3 by ring] at h₂
      linarith
    have h11 : f (x + 4) ≤ f (x + 3) + 1 := by
      specialize h₂ (x + 3)
      rw [show x + 3 + 1 = x + 4 by ring] at h₂
      linarith
    have h12 : f (x + 5) ≤ f (x + 4) + 1 := by
      specialize h₂ (x + 4)
      rw [show x + 4 + 1 = x + 5 by ring] at h₂
      linarith
    -- Adding up all the inequalities
    have h13 : f (x + 1) = f x + 1 := by
      linarith
    exact h13

  have h7 : ∀ (n : ℕ), f (1 + (↑n : ℝ)) = 1 + (↑n : ℝ) := by
    intro n
    induction n with
    | zero =>
      norm_num
      all_goals linarith [h₄]
    | succ n ih =>
      have h9 : (1 + ((↑(n + 1 : ℕ) : ℝ)) ) = (1 + ((↑(n : ℕ) : ℝ)) ) + 1 := by
        simp at *
        all_goals ring
      rw [h9]
      have h10 : f ((1 + ((↑(n : ℕ) : ℝ)) ) + 1) = f (1 + ((↑(n : ℕ) : ℝ)) ) + 1 := by
        specialize h5 (1 + ((↑(n : ℕ) : ℝ)) )
        simpa using h5
      rw [h10, ih]
      all_goals
        simp at *
        all_goals linarith

  have h10 : f 2002 = 2002 := by
    specialize h7 2001
    norm_num at h7 ⊢
    linarith

  have h11 : g 2002 = f 2002 + 1 - 2002 := by
    rw [h₃]

  rw [h11, h10]
  all_goals
    norm_num