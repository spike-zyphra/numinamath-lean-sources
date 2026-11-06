import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_9131 {f : ℝ → ℝ} (hf : f = λ x => sin x * cos x) :
    IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (Real.pi) := by
  constructor
  · -- First, show that π is a positive period.
    constructor
    · -- Show that 0 < π
      exact pi_pos
    · -- Show that f = fun x => f (x + π)
      funext x
      have h1 : sin (x + Real.pi) = - sin x := Real.sin_add_pi x
      have h2 : cos (x + Real.pi) = - cos x := Real.cos_add_pi x
      calc
        f x = sin x * cos x := by rw [hf]
        _ = (- sin x) * (- cos x) := by ring
        _ = sin (x + Real.pi) * cos (x + Real.pi) := by rw [h1, h2]
        _ = f (x + Real.pi) := by rw [hf]
  · -- Now, show that π is the smallest.
    intro T ⟨hT_pos, h_eq⟩
    by_contra h
    push_neg at h
    -- Assume T > 0 and T < π.
    have h1 : T < Real.pi := by linarith
    -- Let's take x = π/2 - T/2.
    have h3 : ∀ x, f x = f (x + T) := by
      intro x
      simpa using congr_fun h_eq x
    -- Let's take x = π/2 - T/2.
    have h4 := h3 (Real.pi / 2 - T / 2)
    -- Calculate the expressions for f(x) and f(x + T).
    have h5 : sin (Real.pi / 2 - T / 2) = cos (T / 2) := by
      have h : sin (Real.pi / 2 - T / 2) = cos (T / 2) := by
        rw [show Real.pi / 2 - T / 2 = Real.pi / 2 - (T / 2) by ring]
        rw [sin_pi_div_two_sub]
      exact h
    have h6 : cos (Real.pi / 2 - T / 2) = sin (T / 2) := by
      have h : cos (Real.pi / 2 - T / 2) = sin (T / 2) := by
        rw [show Real.pi / 2 - T / 2 = Real.pi / 2 - (T / 2) by ring]
        rw [cos_pi_div_two_sub]
      exact h
    have h7 : sin (Real.pi / 2 - T / 2 + T) = cos (T / 2) := by
      have h8 : Real.pi / 2 - T / 2 + T = Real.pi / 2 + T / 2 := by ring
      rw [h8]
      have h9 : sin (Real.pi / 2 + T / 2) = cos (T / 2) := by
        rw [show Real.pi / 2 + T / 2 = Real.pi / 2 + (T / 2) by ring]
        rw [sin_add, sin_pi_div_two, cos_pi_div_two]
        ring
      exact h9
    have h8 : cos (Real.pi / 2 - T / 2 + T) = - sin (T / 2) := by
      have h9 : Real.pi / 2 - T / 2 + T = Real.pi / 2 + T / 2 := by ring
      rw [h9]
      have h10 : cos (Real.pi / 2 + T / 2) = - sin (T / 2) := by
        rw [show Real.pi / 2 + T / 2 = Real.pi / 2 + (T / 2) by ring]
        rw [cos_add, sin_pi_div_two, cos_pi_div_two]
        ring
      exact h10
    -- Now compute f(x) and f(x + T).
    have h9 : f (Real.pi / 2 - T / 2) = f (Real.pi / 2 - T / 2 + T) := by
      simpa using h4
    -- Now compute f(x) and f(x + T).
    have h11 : f (Real.pi / 2 - T / 2) = sin (Real.pi / 2 - T / 2) * cos (Real.pi / 2 - T / 2) := by 
      rw [hf]
    have h12 : f (Real.pi / 2 - T / 2 + T) = sin (Real.pi / 2 - T / 2 + T) * cos (Real.pi / 2 - T / 2 + T) := by 
      rw [hf]
    rw [h11, h12] at h9
    rw [h5, h6, h7, h8] at h9
    have h13 : 2 * cos (T / 2) * sin (T / 2) = 0 := by
      nlinarith
    have h14 : sin T = 0 := by
      have h15 : sin T = 2 * sin (T / 2) * cos (T / 2) := by
        rw [←Real.sin_two_mul]
        all_goals ring_nf
      nlinarith [h15, h13]
    -- Show contradiction with sin T > 0 for T ∈ (0, π).
    have h15 : sin T > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith
    linarith