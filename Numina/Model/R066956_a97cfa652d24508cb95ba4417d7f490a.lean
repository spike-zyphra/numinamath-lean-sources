import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_319440 {f : ℝ → ℝ} (hf : f = λ x => (cos x)^4 + (sin x)^2) :
    IsLeast {x | 0 < x ∧ f = λ y => f (y + x)} (π / 2) := by
  constructor
  · -- Show that π / 2 is in the set
    constructor
    · -- Show that π / 2 > 0
      linarith [Real.pi_pos]
    · -- Show that f = λ y => f (y + π / 2)
      funext y
      rw [hf]
      have h1 : cos (y + π / 2) = -sin y := by
        rw [cos_add, cos_pi_div_two, sin_pi_div_two]
        ring
      have h2 : sin (y + π / 2) = cos y := by
        rw [sin_add, cos_pi_div_two, sin_pi_div_two]
        ring
      simp [h1, h2]
      have h3 : cos y ^ 4 + (sin y) ^ 2 = (sin y) ^ 4 + cos y ^ 2 := by
        have h4 : cos y ^ 2 + (sin y) ^ 2 = 1 := by
          exact Real.cos_sq_add_sin_sq y
        nlinarith [sq_nonneg (cos y ^ 2 - (sin y) ^ 2)]
      linarith [h3]
  · -- Show that π / 2 is the smallest
    intro x hx
    rcases hx with ⟨hx_pos, hx_period⟩
    rw [hf] at hx_period
    have eq1 := congr_fun hx_period 0
    simp [hf] at eq1 
    have eq2 := congr_fun hx_period (π / 2)
    simp [hf] at eq2
    have eq1' : cos x ^ 4 + (sin x) ^ 2 = 1 := by
      nlinarith [Real.cos_sq_add_sin_sq x]
    have eq2' : (sin x) ^ 4 + cos x ^ 2 = 1 := by
      nlinarith [Real.cos_sq_add_sin_sq x]
    have h3 : cos x ^ 2 + (sin x) ^ 2 = 1 := Real.cos_sq_add_sin_sq x
    have h4 : sin x = 0 ∨ cos x = 0 := by
      have eq3 : cos x ^ 4 = cos x ^ 2 := by
        nlinarith
      have eq4 : (sin x) ^ 4 = (sin x) ^ 2 := by
        nlinarith
      have h5 : cos x ^ 2 * (cos x ^ 2 - 1) = 0 := by
        nlinarith
      have h6 : (sin x) ^ 2 * ((sin x) ^ 2 - 1) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h5) with
      | inl h7 =>
        have hcos0 : cos x = 0 := by nlinarith
        right
        exact hcos0
      | inr h8 =>
        have hcos1 : cos x ^ 2 = 1 := by nlinarith
        have hsin0 : sin x = 0 := by
          nlinarith [Real.cos_sq_add_sin_sq x]
        left
        exact hsin0
    cases h4 with
    | inl hsin0 =>
      have h1 : x ≥ π / 2 := by
        by_contra h
        push_neg at h
        have hsin_pos : sin x > 0 := by
          apply sin_pos_of_pos_of_lt_pi
          all_goals linarith [Real.pi_pos]
        nlinarith
      linarith
    | inr hcos0 =>
      have h1 : x ≥ π / 2 := by
        by_contra h
        push_neg at h
        have hcos_pos : cos x > 0 := by
          apply cos_pos_of_mem_Ioo
          constructor
          · linarith [Real.pi_pos]
          · linarith [Real.pi_pos]
        nlinarith
      linarith