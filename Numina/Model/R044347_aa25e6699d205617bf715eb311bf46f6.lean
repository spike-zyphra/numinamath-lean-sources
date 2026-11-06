import Mathlib

open Real Set

theorem inequalities_289208 (f : ℝ → ℝ) :
    (∀ x, f (sin x) ≤ cos (2 * x)) ↔ ∀ x ∈ Icc (-1) 1, f x ≤ 1 - 2 * x ^ 2 := by
  constructor
  · -- Proof of the first direction: ∀ x, f (sin x) ≤ cos (2 * x) implies ∀ x ∈ Icc (-1) 1, f x ≤ 1 - 2 * x ^ 2
    intro h x hx
    rcases hx with ⟨hx1, hx2⟩
    have h3 : ∃ θ, sin θ = x := by 
      use arcsin x
      apply sin_arcsin
      all_goals linarith
    rcases h3 with ⟨θ, hsin⟩
    have h4 : f x ≤ cos (2 * θ) := by
      have h5 : sin θ = x := hsin
      have h6 : f (sin θ) ≤ cos (2 * θ) := h θ
      rw [show sin θ = x by linarith] at h6
      linarith
    have h5 : cos (2 * θ) = 1 - 2 * x ^ 2 := by
      have h6 : cos (2 * θ) = 1 - 2 * (sin θ) ^ 2 := by 
        rw [cos_two_mul, sin_sq]
        <;> ring
      rw [h6]
      rw [show sin θ = x by linarith]
    linarith
  · -- Proof of the second direction: ∀ x ∈ Icc (-1) 1, f x ≤ 1 - 2 * x ^ 2 implies ∀ x, f (sin x) ≤ cos (2 * x)
    intro h x
    have h6 : f (sin x) ≤ 1 - 2 * (sin x) ^ 2 := by
      apply h (sin x) 
      constructor
      all_goals linarith [neg_one_le_sin x, sin_le_one x]
    have h7 : 1 - 2 * (sin x) ^ 2 = cos (2 * x) := by 
      have h8 : cos (2 * x) = 1 - 2 * (sin x) ^ 2 := by
        rw [cos_two_mul, sin_sq]
        <;> ring
      linarith
    linarith [h6, h7]