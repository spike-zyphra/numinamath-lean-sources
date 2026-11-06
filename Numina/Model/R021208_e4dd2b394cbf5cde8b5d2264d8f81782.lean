import Mathlib

open Real Set
open scoped Real

theorem inequalities_139022 (s : Finset ℝ) (h₀ : s.card = 4)
  (h₁ : ∀ x ∈ s, x ∈ Ioo 0 (π/2)) :
  ∃ x ∈ s, ∃ y ∈ s, 8 * cos x * cos y * cos (x - y) + 1 > 4 * (cos x ^ 2 + cos y ^ 2) := by
  have h2 : s.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    by_contra h
    rw [h] at h₀
    simp at h₀
  rcases h2 with ⟨x, hx⟩
  use x, hx
  use x, hx
  have hx1 : x ∈ s := by simpa using hx
  have h3 : 0 < x := by
    have h2 := h₁ x hx1
    exact h2.left
  have h4 : x < π / 2 := by
    have h2 := h₁ x hx1
    exact h2.right
  have h5 : cos (x - x) = 1 := by
    simp [cos_zero]
  have h6 : 8 * cos x * cos x * cos (x - x) + 1 > 4 * (cos x ^ 2 + cos x ^ 2) := by
    rw [show cos (x - x) = 1 by
        apply h5
    ]
    have h8 : cos x ^ 2 ≥ 0 := by
      nlinarith [cos_sq_add_sin_sq x, sq_nonneg (cos x), sq_nonneg (sin x)]
    nlinarith [h8]
  simpa using h6