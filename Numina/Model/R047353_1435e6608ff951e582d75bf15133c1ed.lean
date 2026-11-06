import Mathlib

open BigOperators Complex Filter Finset Real TopologicalSpace Topology

theorem inequalities_171125 (f : ℝ → ℝ) :
    (∀ x y z, f (x + y) + f (y + z) + f (z + x) ≥ 3 * f (x + 2 * y + 3 * z)) ↔
    ∃ c, ∀ x, f x = c := by
  constructor
  · -- Assume the inequality holds, prove f is constant
    intro h
    have h1 : ∀ a b : ℝ, f a + f 0 ≥ 2 * f b := by
      intro a b
      have h2 := h ((a + b) / 2) ((a - b) / 2) ((b - a) / 2)
      have h3 : f (( (a + b) / 2 + (a - b) / 2 )) + f (( (a - b) / 2 + (b - a) / 2 )) + f (( (b - a) / 2 + (a + b) / 2 )) ≥ 3 * f ( ( (a + b) / 2 ) + 2 * ( (a - b) / 2 ) + 3 * ( (b - a) / 2 ) ) := by
        simpa using h2
      have h4 : f (( (a + b) / 2 + (a - b) / 2 )) = f a := by
        ring_nf
      have h5 : f (( (a - b) / 2 + (b - a) / 2 )) = f 0 := by
        ring_nf
      have h6 : f (( (b - a) / 2 + (a + b) / 2 )) = f b := by
        ring_nf
      have h7 : f ( ( (a + b) / 2 ) + 2 * ( (a - b) / 2 ) + 3 * ( (b - a) / 2 ) ) = f b := by
        ring_nf
      rw [h4, h5, h6, h7] at h3
      linarith
    -- From h1, we can show f x ≤ f 0.
    have h2 : ∀ x : ℝ, f x ≤ f 0 := by
      intro x
      have h17 := h1 x x
      linarith
    -- From h1, we can show f x ≥ f 0.
    have h3 : ∀ x : ℝ, f x ≥ f 0 := by
      intro x
      have h17 := h1 x 0
      simp at h17
      linarith
    use f 0
    intro x
    have h4 := h2 x
    have h5 := h3 x
    linarith
  · -- Assume f is a constant function, prove the inequality
    rintro ⟨c, hc⟩
    intro x y z
    have h1 : f (x + y) = c := by
      rw [hc (x + y)]
    have h2 : f (y + z) = c := by
      rw [hc (y + z)]
    have h3 : f (z + x) = c := by
      rw [hc (z + x)]
    have h4 : f (x + 2 * y + 3 * z) = c := by
      rw [hc (x + 2 * y + 3 * z)]
    rw [h1, h2, h3, h4]
    all_goals linarith