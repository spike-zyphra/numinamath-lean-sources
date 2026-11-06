import Mathlib

theorem algebra_210363 {f : ℝ → ℝ} (h : ∀ x, f (x - 2) = f x)
    (hf : ∀ x ∈ Set.Icc (-1) 1, f x = x ^ 2 - 2 * x + 4) :
    ∀ x ∈ Set.Icc (-3) (-1), f x = x ^ 2 + 2 * x + 4 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have h1 : f x = f (x + 2) := by
    specialize h (x + 2)
    ring_nf at h ⊢
    linarith
  have hx2 : (x + 2) ∈ Set.Icc (-1) 1 := by
    rw [Set.mem_Icc]
    constructor
    · linarith
    · linarith
  have hfx2 := hf (x + 2) hx2
  rw [h1, hfx2]
  ring