import Mathlib


lemma lemma_1 {f : ℝ → ℝ} (h1 : ∀ x, f (x + 5) ≥ f x + 5) (h2 : ∀ x, f (x + 1) ≤ f x + 1) :
    ∀ x, f x - x = f (x + 1) - (x + 1) := by
  intro x
  have h3 : f (x + 5) = f x + 5 := by
    have h4 : f (x + 5) ≥ f x + 5 := h1 x
    have h5 : f (x + 5) ≤ f x + 5 := by
      have h6 : f (x + 1) ≤ f x + 1 := h2 x
      have h7 : f (x + 2) ≤ f (x + 1) + 1 := by
        specialize h2 (x + 1)
        rw [show x + 1 + 1 = x + 2 by ring] at h2
        linarith
      have h8 : f (x + 3) ≤ f (x + 2) + 1 := by
        specialize h2 (x + 2)
        rw [show x + 2 + 1 = x + 3 by ring] at h2
        linarith
      have h9 : f (x + 4) ≤ f (x + 3) + 1 := by
        specialize h2 (x + 3)
        rw [show x + 3 + 1 = x + 4 by ring] at h2
        linarith
      have h10 : f (x + 5) ≤ f (x + 4) + 1 := by
        specialize h2 (x + 4)
        rw [show x + 4 + 1 = x + 5 by ring] at h2
        linarith
      linarith [h6, h7, h8, h9, h10]
    linarith
  have h4 : f (x + 1) = f x + 1 := by
    have h5 : f (x + 5) = f x + 5 := h3
    have h6 : f (x + 1) ≤ f x + 1 := h2 x
    have h7 : f (x + 2) ≤ f (x + 1) + 1 := by
      specialize h2 (x + 1)
      rw [show x + 1 + 1 = x + 2 by ring] at h2
      linarith
    have h8 : f (x + 3) ≤ f (x + 2) + 1 := by
      specialize h2 (x + 2)
      rw [show x + 2 + 1 = x + 3 by ring] at h2
      linarith
    have h9 : f (x + 4) ≤ f (x + 3) + 1 := by
      specialize h2 (x + 3)
      rw [show x + 3 + 1 = x + 4 by ring] at h2
      linarith
    have h10 : f (x + 5) ≤ f (x + 4) + 1 := by
      specialize h2 (x + 4)
      rw [show x + 4 + 1 = x + 5 by ring] at h2
      linarith
    linarith [h5, h6, h7, h8, h9, h10]
  linarith [h4]


theorem algebra_222706 (f : ℝ → ℝ) (g : ℝ → ℝ) (hf1 : f 1 = 1)
    (hfx : ∀ x, f (x + 5) ≥ f x + 5 ∧ f (x + 1) ≤ f x + 1)
    (hg : g = fun x => f x + 1 - x) :
    g 2009 = 1 := by
  have h1 : ∀ x, f (x + 5) ≥ f x + 5 := by
    intro x
    exact (hfx x).1
  have h2 : ∀ x, f (x + 1) ≤ f x + 1 := by
    intro x
    exact (hfx x).2
  have h4 : ∀ x, f (x + 1) = f x + 1 := by
    intro x
    have h5 : f (x + 5) = f x + 5 := by
      have h4 : f (x + 5) ≥ f x + 5 := h1 x
      have h5 : f (x + 5) ≤ f x + 5 := by
        have h6 : f (x + 1) ≤ f x + 1 := h2 x
        have h7 : f (x + 2) ≤ f (x + 1) + 1 := by
          specialize h2 (x + 1)
          rw [show x + 1 + 1 = x + 2 by ring] at h2
          linarith
        have h8 : f (x + 3) ≤ f (x + 2) + 1 := by
          specialize h2 (x + 2)
          rw [show x + 2 + 1 = x + 3 by ring] at h2
          linarith
        have h9 : f (x + 4) ≤ f (x + 3) + 1 := by
          specialize h2 (x + 3)
          rw [show x + 3 + 1 = x + 4 by ring] at h2
          linarith
        have h10 : f (x + 5) ≤ f (x + 4) + 1 := by
          specialize h2 (x + 4)
          rw [show x + 4 + 1 = x + 5 by ring] at h2
          linarith
        linarith [h6, h7, h8, h9, h10]
      linarith
    have h6 : f (x + 1) ≤ f x + 1 := h2 x
    have h7 : f (x + 2) ≤ f (x + 1) + 1 := by
      specialize h2 (x + 1)
      rw [show x + 1 + 1 = x + 2 by ring] at h2
      linarith
    have h8 : f (x + 3) ≤ f (x + 2) + 1 := by
      specialize h2 (x + 2)
      rw [show x + 2 + 1 = x + 3 by ring] at h2
      linarith
    have h9 : f (x + 4) ≤ f (x + 3) + 1 := by
      specialize h2 (x + 3)
      rw [show x + 3 + 1 = x + 4 by ring] at h2
      linarith
    have h10 : f (x + 5) ≤ f (x + 4) + 1 := by
      specialize h2 (x + 4)
      rw [show x + 4 + 1 = x + 5 by ring] at h2
      linarith
    linarith [h5, h6, h7, h8, h9, h10]
  have hf2009 : f 2009 = 2009 := by
    have h7 : ∀ (n : ℕ), f (1 + (n : ℝ)) = 1 + (n : ℝ) := by
      intro n
      induction n with
      | zero =>
        norm_num
        all_goals linarith [hf1]
      | succ n ih =>
        have h8 : (1 + ((n + 1 : ℕ) : ℝ) : ℝ) = (1 + ((n : ℕ) : ℝ) : ℝ) + 1 := by
          simp at *
          all_goals
          ring
        rw [h8]
        have h9 : f ((1 + ((n : ℕ) : ℝ) : ℝ) + 1) = f (1 + ((n : ℕ) : ℝ) : ℝ) + 1 := by
          specialize h4 (1 + ((n : ℕ) : ℝ) : ℝ)
          simpa using h4
        rw [h9, ih]
        all_goals
        simp at *
        all_goals
        linarith
    specialize h7 2008
    norm_num at h7 ⊢
    linarith [h7]
  have g2009 : g 2009 = f 2009 + 1 - (2009 : ℝ) := by
    rw [hg]
  rw [g2009]
  linarith [hf2009]