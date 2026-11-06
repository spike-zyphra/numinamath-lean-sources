import Mathlib

theorem algebra_195241 {f : ℝ → ℝ} (h1 : f 1 = 1) (h2 : ∀ x, f (x + 5) ≥ f x + 5) (h3 : ∀ x, f (x + 1) ≤ f x + 1)
    (g : ℝ → ℝ) (hg : g = fun x => f x + 1 - x) : g 2002 = 1 := by

  have h4 : ∀ x, f (x + 1) = f x + 1 := by
    intro x

    have h5 : f (x + 5) ≥ f x + 5 := h2 x

    -- Apply h3 5 times to derive an upper bound for f(x + 5)
    have h6 : f (x + 5) ≤ f (x + 4) + 1 := by
      specialize h3 (x + 4)
      ring_nf at h3 ⊢
      linarith

    have h7 : f (x + 4) ≤ f (x + 3) + 1 := by
      specialize h3 (x + 3)
      ring_nf at h3 ⊢
      linarith

    have h8 : f (x + 3) ≤ f (x + 2) + 1 := by
      specialize h3 (x + 2)
      ring_nf at h3 ⊢
      linarith

    have h9 : f (x + 2) ≤ f (x + 1) + 1 := by
      specialize h3 (x + 1)
      ring_nf at h3 ⊢
      linarith

    have h10 : f (x + 1) ≤ f x + 1 := h3 x

    have h11 : f (x + 5) ≤ f x + 5 := by
      linarith [h6, h7, h8, h9, h10]

    have h12 : f (x + 5) = f x + 5 := by
      linarith [h5, h11]

    linarith [h12, h6, h7, h8, h9, h10]

  have h7 : ∀ (n : ℕ), f (1 + (↑n : ℝ)) = 1 + (↑n : ℝ) := by
    intro n
    induction n with
    | zero =>
      norm_num [h1]
    | succ n ih =>
      have eq1 : (1 + ((↑(n + 1) : ℕ) : ℝ)) = (1 + (↑n : ℝ) ) + 1 := by
        simp at *
        <;> ring
      rw [eq1]
      rw [h4]
      rw [ih]
      all_goals norm_num
      <;> ring

  -- Prove f(2002) = 2002
  have h8 : f 2002 = 2002 := by
    specialize h7 2001
    norm_num at h7 ⊢
    linarith

  -- Compute g(2002)
  have h9 : g 2002 = f 2002 + 1 - (2002 : ℝ) := by
    rw [hg]
    all_goals norm_num

  rw [h9]
  rw [h8]
  all_goals norm_num