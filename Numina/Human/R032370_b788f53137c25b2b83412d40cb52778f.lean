import Mathlib

open Real

/- What is the period of the function $f(x)=\cos (\cos (x))$ ?-/
theorem algebra_608562 (f : ℝ → ℝ) (hf : ∀ x, f x = cos (cos x)):
    IsLeast {T : ℝ | 0 < T ∧ ∀ x, f (x + T) = f x} π := by
  -- Simplify the goal into two parts.
  simp only [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- Show that π belongs to the set.
    simp [pi_pos, hf]
  . -- Show that π is the least such number.
    simp
    intro T hT hx
    -- Specialize the period hypothesis to 0.
    specialize hx 0
    simp [hf] at hx
    -- Assume on the contrary that π > T.
    by_contra! hT'
    -- Show that cos T ∈ (-1, 1).
    have hcosT : cos T ∈ Set.Ioo (-1) 1 := by
      refine ⟨?_, ?_⟩
      . -- Show that -1 < cos T.
        apply lt_of_le_of_ne
        . apply neg_one_le_cos
        . by_contra!
          symm at this
          rw [cos_eq_neg_one_iff] at this
          obtain ⟨k, this⟩ := this
          linarith [show k < 0 by rify; nlinarith, show k > -1 by rify; nlinarith]
      . -- Show that cos T < 1.
        apply lt_of_le_of_ne
        . apply cos_le_one
        . by_contra!
          rw [cos_eq_one_iff_of_lt_of_lt] at this
          <;> linarith [pi_pos]
    -- Show that cos (cos T) > cos 1.
    have hx' : cos (cos T) > cos 1 := by
      rw [<-Real.cos_abs]
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      . apply abs_nonneg
      . linarith [pi_gt_three]
      . simp at hcosT
        simp [abs_lt, hcosT]
    -- A contradiction is derived.
    linarith only [hx, hx']

