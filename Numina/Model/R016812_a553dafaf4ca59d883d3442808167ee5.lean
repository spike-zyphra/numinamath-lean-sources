import Mathlib


theorem algebra_307975 {f : ℝ → ℝ} (h1 : ∀ x, f (x + 1) + f (1 - x) = 0) (h2 : ∀ x, f (x + 2) - f (2 - x) = 0)
    (hf : f (2 / 3) = 1) : f (1000 / 3) = -1 := by

  have h3 : ∀ x, f (x + 3) = -f (x + 1) := by
    intro x
    have eq1 := h2 (x + 1)
    have eq2 := h1 (x + 1)
    have eq3 : f ((x + 1) + 2) = f (2 - (x + 1)) := by linarith [eq1]
    have eq4 : f (x + 3) = f (1 - x) := by
      ring_nf at eq3 ⊢
      linarith
    have eq5 : f (1 - x) = -f (x + 1) := by
      have eq6 := h1 x
      have eq7 : f (x + 1) + f (1 - x) = 0 := by
        simpa using eq6
      linarith
    linarith [eq4, eq5]

  have h4 : ∀ x, f (x + 4) = f x := by
    intro x
    have eq1 := h3 x
    have eq2 := h3 (x + 1)
    have eq3 := h3 (x - 1)
    have eq6 : f (x + 4) = -f (x + 2) := by
      ring_nf at eq2 ⊢
      linarith
    have eq7 : f (x + 2) = -f x := by
      have eq9 : f ((x - 1) + 3) = -f ((x - 1) + 1) := by
        simpa using eq3
      ring_nf at eq9 ⊢
      linarith
    linarith [eq6, eq7]

  have h5 : f (1000 / 3) = f (4 / 3) := by
    have eq3 : (1000 / 3 : ℝ) = (4 / 3 : ℝ) + (83 : ℝ) * 4 := by
      norm_num
    rw [eq3]
    have h6 : ∀ k : ℕ, f (4 / 3 + (k : ℝ) * 4) = f (4 / 3) := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        have eq1 : (4 / 3 + ((k + 1 : ℕ) : ℝ) * 4) = (4 / 3 + ((k : ℕ) : ℝ) * 4) + (4 : ℝ) := by
          simp at *
          ring_nf
        rw [eq1]
        have eq2 : f ((4 / 3 + ((k : ℕ) : ℝ) * 4) + (4 : ℝ)) = f (4 / 3 + ((k : ℕ) : ℝ) * 4) := by
          have eq3 : f ((4 / 3 + ((k : ℕ) : ℝ) * 4) + 4) = f (4 / 3 + ((k : ℕ) : ℝ) * 4) := by
            apply h4
          ring_nf at eq3 ⊢
          all_goals linarith
        linarith [eq2, ih]
    specialize h6 83
    norm_num at h6 ⊢
    linarith

  have h7 : f (4 / 3) = -1 := by
    have eq1 : f (4 / 3) + f (2 / 3) = 0 := by
      have eq1 := h1 (1 / 3)
      have eq2 : f ((1 / 3 : ℝ) + 1) + f (1 - (1 / 3 : ℝ)) = 0 := by
        simpa using eq1
      have eq3 : f (4 / 3) + f (2 / 3) = 0 := by
        ring_nf at eq2 ⊢
        linarith
      linarith
    have eq2 : f (2 / 3) = 1 := hf
    linarith

  linarith [h5, h7]