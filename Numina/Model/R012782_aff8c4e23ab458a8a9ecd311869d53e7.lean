import Mathlib

theorem algebra_109770 (f : ℝ → ℝ) (h₁ : f 1 = 1) (h₂ : ∀ x, f (x + 5) ≥ f x + 5)
    (h₃ : ∀ x, f (x + 1) ≤ f x + 1) (g : ℝ → ℝ) (hg : g = fun x => f x + 1 - x) :
    g 2002 = 1 := by
  have H1 : ∀ x, f (x + 1) = f x + 1 := by
    intro x
    have h4 : f (x + 5) ≥ f x + 5 := h₂ x
    have h5 : f (x + 5) ≤ f (x + 4) + 1 := by
      specialize h₃ (x + 4)
      rw [show x + 4 + 1 = x + 5 by ring] at h₃
      linarith
    have h6 : f (x + 4) ≤ f (x + 3) + 1 := by
      specialize h₃ (x + 3)
      rw [show x + 3 + 1 = x + 4 by ring] at h₃
      linarith
    have h7 : f (x + 3) ≤ f (x + 2) + 1 := by
      specialize h₃ (x + 2)
      rw [show x + 2 + 1 = x + 3 by ring] at h₃
      linarith
    have h8 : f (x + 2) ≤ f (x + 1) + 1 := by
      specialize h₃ (x + 1)
      rw [show x + 1 + 1 = x + 2 by ring] at h₃
      linarith
    have h9 : f (x + 1) ≤ f x + 1 := by
      specialize h₃ x
      rw [show x + 1 = x + 1 by rfl] at h₃
      linarith
    have h11 : f (x + 5) = f x + 5 := by
      linarith [h4, h5, h6, h7, h8, h9]
    have h12 : f (x + 1) = f x + 1 := by
      nlinarith [h11, h5, h6, h7, h8, h9]
    linarith

  -- Let's prove by induction that f(1 + n) = 1 + n for all n ∈ ℕ.
  have H2 : ∀ (n : ℕ), f (1 + (↑n : ℝ)) = 1 + (↑n : ℝ) := by
    intro n
    induction n with
    | zero =>
      norm_num
      all_goals norm_num [h₁]
    | succ n ih =>
      have eq1 : (1 + ((↑(n + 1 : ℕ) : ℝ)) : ℝ) = (1 + ((↑n : ℝ)) : ℝ) + 1 := by
        simp at *
        all_goals linarith
      rw [eq1]
      have eq2 : f ((1 + ((↑n : ℝ)) : ℝ) + 1) = f (1 + ((↑n : ℝ)) : ℝ) + 1 := by
        specialize H1 (1 + ((↑n : ℝ)) : ℝ)
        linarith
      rw [eq2, ih]
      all_goals
        norm_num at *
        all_goals linarith

  -- Compute 2002 = 1 + 2001.
  have eq1 : (2002 : ℝ) = 1 + (↑(2001 : ℕ) : ℝ) := by
    norm_num

  -- Compute f(2002).
  have eq2 : f 2002 = 2002 := by
    rw [eq1] at *
    specialize H2 2001
    norm_num at H2 ⊢
    linarith

  -- Compute g(2002).
  have eq3 : g 2002 = f 2002 + 1 - (2002 : ℝ) := by
    rw [hg]

  rw [eq3]
  rw [eq2]
  all_goals norm_num