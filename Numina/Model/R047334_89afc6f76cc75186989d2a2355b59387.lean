import Mathlib

theorem algebra_299670 {f : ℝ → ℝ} (hf : ∀ x, f (x + 1) * f (x - 1) = f x)
    (hpos : ∀ x, f x > 0) :
    f (x + 6) = f x := by
  have eq1 : f (x + 2) * f x = f (x + 1) := by
    specialize hf (x + 1)
    have h1 : f ((x + 1) + 1) * f ((x + 1) - 1) = f (x + 1) := by
      simpa using hf
    have h2 : f ((x + 1) + 1) = f (x + 2) := by ring_nf
    have h3 : f ((x + 1) - 1) = f x := by ring_nf
    rw [h2, h3] at h1
    linarith

  have eq2 : f (x + 3) * f (x + 1) = f (x + 2) := by
    specialize hf (x + 2)
    have h1 : f ((x + 2) + 1) * f ((x + 2) - 1) = f (x + 2) := by
      simpa using hf
    have h2 : f ((x + 2) + 1) = f (x + 3) := by ring_nf
    have h3 : f ((x + 2) - 1) = f (x + 1) := by ring_nf
    rw [h2, h3] at h1
    linarith

  have eq3 : f (x + 4) * f (x + 2) = f (x + 3) := by
    specialize hf (x + 3)
    have h1 : f ((x + 3) + 1) * f ((x + 3) - 1) = f (x + 3) := by
      simpa using hf
    have h2 : f ((x + 3) + 1) = f (x + 4) := by ring_nf
    have h3 : f ((x + 3) - 1) = f (x + 2) := by ring_nf
    rw [h2, h3] at h1
    linarith

  have eq4 : f (x + 5) * f (x + 3) = f (x + 4) := by
    specialize hf (x + 4)
    have h1 : f ((x + 4) + 1) * f ((x + 4) - 1) = f (x + 4) := by
      simpa using hf
    have h2 : f ((x + 4) + 1) = f (x + 5) := by ring_nf
    have h3 : f ((x + 4) - 1) = f (x + 3) := by ring_nf
    rw [h2, h3] at h1
    linarith

  have eq5 : f (x + 6) * f (x + 4) = f (x + 5) := by
    specialize hf (x + 5)
    have h1 : f ((x + 5) + 1) * f ((x + 5) - 1) = f (x + 5) := by
      simpa using hf
    have h2 : f ((x + 5) + 1) = f (x + 6) := by ring_nf
    have h3 : f ((x + 5) - 1) = f (x + 4) := by ring_nf
    rw [h2, h3] at h1
    linarith

  have h1 : f (x + 2) = f (x + 1) / f x := by
    have h2 : f x > 0 := hpos x
    field_simp
    nlinarith [eq1]

  have h2 : f (x + 3) = 1 / f x := by
    have h3 : f (x + 2) = f (x + 1) / f x := h1
    have h4 : f (x + 3) * f (x + 1) = f (x + 2) := eq2
    rw [h3] at h4
    have h5 : f (x + 1) > 0 := hpos (x + 1)
    have h6 : f x > 0 := hpos x
    field_simp at h4 ⊢
    nlinarith [h4, h5, h6]

  have h3 : f (x + 4) = 1 / f (x + 1) := by
    have h4 : f (x + 4) * f (x + 2) = f (x + 3) := eq3
    rw [h1, h2] at h4
    have h5 : f (x + 1) > 0 := hpos (x + 1)
    have h6 : f x > 0 := hpos x
    field_simp at h4 ⊢
    nlinarith [h4, h5, h6]

  have h4 : f (x + 5) = f x / f (x + 1) := by
    have h5 : f (x + 5) * f (x + 3) = f (x + 4) := eq4
    rw [h2, h3] at h5
    have h6 : f (x + 1) > 0 := hpos (x + 1)
    have h7 : f x > 0 := hpos x
    field_simp at h5 ⊢
    nlinarith [h5, h6, h7]

  have h5 : f (x + 6) = f x := by
    have h8 : f (x + 6) * f (x + 4) = f (x + 5) := eq5
    rw [h3, h4] at h8
    have h6 : f (x + 1) > 0 := hpos (x + 1)
    have h7 : f x > 0 := hpos x
    field_simp at h8 ⊢
    nlinarith [h8, h6, h7]

  exact h5