import Mathlib

theorem algebra_115811 {f : ℝ → ℝ} (h : ∀ x y, f (x * f x + f x * f y + y - 1) = f (x * f x + x * y) + y - 1) :
    ∀ x, f x = x := by
  have h0 : ∀ y, f (f 0 * f y + y - 1) = f 0 + y - 1 := by
    intro y
    specialize h 0 y
    simpa using h

  have hf_surj : ∀ z, ∃ x, f x = z := by
    intro z
    use f 0 * f (z + 1 - f 0) + (z + 1 - f 0) - 1
    have h2 := h0 (z + 1 - f 0)
    ring_nf at h2 ⊢
    linarith

  obtain ⟨t, ht⟩ := hf_surj 0

  have ht_eq1 : ∀ y, f (y - 1) = f (t * y) + y - 1 := by
    intro y
    have ht_eq := h t y
    rw [ht] at ht_eq
    simp at ht_eq 
    linarith

  have h1 : f 0 = 0 := by
    have h2 := ht_eq1 1
    simp at h2 
    linarith [ht, h2]

  have h2 : ∀ y, f (y - 1) = y - 1 := by
    intro y
    specialize h0 y
    rw [h1] at h0
    simp at h0 
    linarith

  intro x 
  have h3 : f x = x := by 
    calc
      f x = f ((x + 1) - 1) := by ring_nf
      _ = (x + 1) - 1 := by rw [h2 (x + 1)]
      _ = x := by ring_nf
  exact h3