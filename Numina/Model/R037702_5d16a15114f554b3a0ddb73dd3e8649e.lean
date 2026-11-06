import Mathlib

theorem algebra_181417 (f : ℝ → ℝ) (hf : f = fun x => -x^2 + 6 * x - 7)
    (t : ℝ) (ht : t ≤ t + 2) (y_max : ℝ) (hy_max : y_max = -(t - 3)^2 + 2) :
    IsGreatest (Set.image f (Set.Icc t (t + 2))) y_max ↔ t ≥ 3 := by
  constructor
  · -- =>
    intro h
    have h1 : ∀ x, x ∈ Set.Icc t (t + 2) → f x ≤ y_max := by
      rcases h with ⟨h2, h3⟩
      intro x hx
      have h4 : f x ∈ Set.image f (Set.Icc t (t + 2)) := by
        use x
        all_goals simp at *
        all_goals try tauto
        all_goals try nlinarith
      have h5 : f x ≤ y_max := by
        apply h3
        exact h4
        all_goals try tauto
      simpa using h5
    by_contra h6
    push_neg at h6
    by_cases h7 : t ≤ 1
    · -- Now we know that the interval is entirely left of the vertex
      -- Since the interval is left of the vertex, the maximum occurs at the right endpoint
      have h8 : f (t + 2) = - (t + 2) ^ 2 + 6 * (t + 2) - 7 := by
        rw [hf]
      have h10 := h1 (t + 2) ⟨by linarith, by linarith⟩
      simp [h8, hy_max] at h10
      nlinarith
    · -- Now we know that 1 < t < 3
      push_neg at h7
      have h8 : 3 ∈ Set.Icc t (t + 2) := by
        constructor
        · -- Show that 3 ≥ t
          nlinarith
        · -- Show that 3 ≤ t + 2
          nlinarith
      have h9 := h1 3 h8
      simp [hf, hy_max] at h9
      nlinarith [sq_nonneg (t - 3)]
  · -- To prove the converse, first show y_max is in the image
    intro h
    constructor
    · -- Show that y_max is in the image
      use t
      constructor
      · -- Show that t is in [t, t + 2]
        exact ⟨by linarith, by linarith⟩
      · -- Show that f(t) = y_max
        simp [hf, hy_max]
        <;> nlinarith
    · -- Show that y_max is greatest in the image
      intro y hy
      rcases hy with ⟨x, hx, hfx⟩
      simp [hf] at hfx
      have h1 : x ∈ Set.Icc t (t + 2) := by
        exact hx
      rcases h1 with ⟨hx1, hx2⟩
      nlinarith [sq_nonneg (x - 3), sq_nonneg (t - 3), sq_nonneg (x - t)]