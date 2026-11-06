import Mathlib

theorem algebra_247468 (f g : ℝ → ℝ)
    (h₁ : ∀ x, f (x + 3) ≤ f x + 3)
    (h₂ : ∀ x, f (x + 2) ≥ f x + 2)
    (h₃ : g = fun x => f x - x)
    (h₄ : f 4 = 2008) :
    f 2008 = 4012 := by
  have h5 : ∀ x, g (x + 2) ≥ g x := by
    intro x
    have h6 : f (x + 2) ≥ f x + 2 := by
      specialize h₂ x
      simpa using h₂
    have eq1 : g (x + 2) = f (x + 2) - (x + 2) := by
      rw [h₃]
      all_goals ring_nf
    have eq2 : g x = f x - x := by
      rw [h₃]
      all_goals ring_nf
    linarith [h6, eq1, eq2]
  have h6 : ∀ x, g (x + 3) ≤ g x := by
    intro x
    have h7 : f (x + 3) ≤ f x + 3 := by
      specialize h₁ x
      simpa using h₁
    have eq1 : g (x + 3) = f (x + 3) - (x + 3) := by
      rw [h₃]
      all_goals ring_nf
    have eq2 : g x = f x - x := by
      rw [h₃]
      all_goals ring_nf
    linarith [h7, eq1, eq2]
  have h7 : ∀ x, g (x + 6) = g x := by
    intro x
    have h8 : g (x + 2) ≥ g x := h5 x
    have h9 : g (x + 3) ≤ g x := h6 x
    have h10 : g (x + 4) ≥ g (x + 2) := by
      specialize h5 (x + 2)
      ring_nf at h5 ⊢
      linarith
    have h11 : g (x + 6) ≤ g (x + 3) := by
      specialize h6 (x + 3)
      ring_nf at h6 ⊢
      linarith
    have h12 : g (x + 6) ≥ g (x + 4) := by
      specialize h5 (x + 4)
      ring_nf at h5 ⊢
      linarith
    linarith [h8, h9, h10, h11, h12]
  have h80 : g 2008 = g 4 := by
    have h9 : ∀ (k : ℕ), g (4 + (k : ℝ) * 6) = g 4 := by
      intro k
      induction k with
      | zero =>
        norm_num
        <;> simp [h₃]
        <;> ring_nf <;> norm_num
        all_goals linarith
      | succ k ih =>
        have eq1 : (4 + ((k + 1 : ℕ) : ℝ) * 6) = (4 + ((k : ℕ) : ℝ) * 6) + 6 := by
          simp at *
          <;> ring_nf <;> norm_num
        rw [eq1]
        have eq2 : g ((4 + ((k : ℕ) : ℝ) * 6) + 6) = g (4 + ((k : ℕ) : ℝ) * 6) := by
          specialize h7 (4 + ((k : ℕ) : ℝ) * 6)
          simpa using h7
        rw [eq2, ih]
    specialize h9 334
    norm_num at h9 ⊢
    <;> linarith [h9]
    all_goals linarith [h9]
  have g4 : g 4 = 2004 := by
    rw [h₃]
    norm_num [h₄]
    all_goals linarith
  have h10 : g 2008 = 2004 := by
    linarith [h80, g4]
  have eq1 : g 2008 = f 2008 - (2008 : ℝ) := by
    rw [h₃]
    all_goals ring_nf
  have eq2 : f 2008 = 4012 := by
    linarith [h10, eq1]
  exact_mod_cast eq2
  all_goals linarith
  all_goals tauto
  all_goals tauto
  all_goals tauto