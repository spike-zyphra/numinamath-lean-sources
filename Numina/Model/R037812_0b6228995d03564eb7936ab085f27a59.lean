import Mathlib

theorem algebra_298281 (f : ℝ → ℝ) (g : ℝ → ℝ) (h₀ : ∀ x, f (x + 3) ≤ f x + 3)
    (h₁ : ∀ x, f (x + 2) ≥ f x + 2) (h₂ : g = fun x => f x - x) (h₃ : f 4 = 2014) :
    f 2014 = 4024 := by

  have h4 : ∀ x : ℝ, f (x + 6) = f x + 6 := by
    intro x
    have h5 : f (x + 6) ≤ f x + 6 := by
      have h6 : f (x + 3) ≤ f x + 3 := by
        specialize h₀ x
        simpa using h₀
      have h7 : f (x + 6) ≤ f (x + 3) + 3 := by
        specialize h₀ (x + 3)
        ring_nf at h₀ ⊢
        all_goals linarith
      linarith
    have h8 : f (x + 6) ≥ f x + 6 := by
      have h9 : f (x + 2) ≥ f x + 2 := by
        specialize h₁ x
        simpa using h₁
      have h10 : f (x + 4) ≥ f (x + 2) + 2 := by
        specialize h₁ (x + 2)
        ring_nf at h₁ ⊢
        all_goals linarith
      have h11 : f (x + 4) ≥ f x + 4 := by
        linarith
      have h12 : f (x + 6) ≥ f (x + 4) + 2 := by
        specialize h₁ (x + 4)
        ring_nf at h₁ ⊢
        all_goals linarith
      linarith
    linarith

  have h5 : ∀ (n : ℕ), f (4 + (n : ℝ) * 6) = 2014 + (n : ℝ) * 6 := by
    intro n
    induction n with
    | zero =>
      norm_num
      all_goals linarith
    | succ n ih =>
      have eq1 : (4 + ((n + 1 : ℕ) : ℝ) * 6) = (4 + ((n : ℕ) : ℝ) * 6) + 6 := by
        simp at *
        <;> norm_num
        <;> ring
      rw [eq1]
      have eq2 : f ((4 + ((n : ℕ) : ℝ) * 6) + 6) = f (4 + ((n : ℕ) : ℝ) * 6) + 6 := by
        specialize h4 (4 + ((n : ℕ) : ℝ) * 6)
        simpa using h4
      rw [eq2]
      rw [ih]
      all_goals simp at *
      <;> linarith

  have h6 : (2014 : ℝ) = 4 + (335 : ℝ) * 6 := by
    norm_num

  rw [h6]
  specialize h5 335
  norm_num at h5 ⊢
  all_goals linarith