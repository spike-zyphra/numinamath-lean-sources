import Mathlib
open Real

theorem algebra_9154 {f : ℝ → ℝ} (hf : f = λ x => cos x ^ 2 - sin x ^ 2) :
    IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} π := by
  constructor
  · -- Show that π is indeed a positive period of f
    constructor
    · -- Show that π > 0
      exact Real.pi_pos
    · -- Show that f = λ x => f (x + π)
      funext x
      have h3 : f x = f (x + π) := by
        rw [hf]
        have h4 : cos x ^ 2 - sin x ^ 2 = cos (x + π) ^ 2 - sin (x + π) ^ 2 := by
          have h5 : cos (x + π) = -cos x := by
            rw [cos_add_pi]
          have h6 : sin (x + π) = -sin x := by
            rw [sin_add_pi]
          rw [h5, h6]
          ring_nf
        simpa using h4
      simpa using h3
  · -- Show that π is the minimal positive period
    intro T hT
    rcases hT with ⟨hT_pos, heq⟩
    by_contra h
    push_neg at h
    -- Assume T < π, derive a contradiction
    have h3 : T < π := h
    -- Apply the function equation at x = π / 2 - T
    have eq1 : f (Real.pi / 2 - T) = f (Real.pi / 2) := by
      have eq2 : f (Real.pi / 2 - T) = f ((Real.pi / 2 - T) + T) := by
        simpa using congr_fun heq (Real.pi / 2 - T)
      have eq3 : (Real.pi / 2 - T : ℝ) + T = Real.pi / 2 := by
        linarith
      rw [eq3] at eq2
      linarith [eq2]
    -- Compute both sides
    have h4 : f (Real.pi / 2 - T) = cos (Real.pi / 2 - T) ^ 2 - sin (Real.pi / 2 - T) ^ 2 := by
      rw [hf]
    have h5 : f (Real.pi / 2) = cos (Real.pi / 2) ^ 2 - sin (Real.pi / 2) ^ 2 := by
      rw [hf]
    rw [h4] at eq1
    rw [h5] at eq1
    -- Simplify using trigonometric identities
    have h6 : cos (Real.pi / 2 - T) = sin T := by
      rw [cos_pi_div_two_sub]
    have h7 : sin (Real.pi / 2 - T) = cos T := by
      rw [sin_pi_div_two_sub]
    have h8 : cos (Real.pi / 2) = 0 := by
      exact cos_pi_div_two
    have h9 : sin (Real.pi / 2) = 1 := by
      exact sin_pi_div_two
    rw [h6, h7, h8, h9] at eq1
    -- We have sin T ^ 2 - cos T ^ 2 = -1
    -- But we also know sin T ^ 2 + cos T ^ 2 = 1
    -- Adding these equations: 2 * sin T ^ 2 = 0 => sin T = 0
    -- This contradicts the fact that sin T > 0 for 0 < T < π
    have h10 : sin T > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [Real.pi_gt_three, h3]
    nlinarith [Real.sin_sq_add_cos_sq T]