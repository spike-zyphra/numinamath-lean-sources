import Mathlib
open Real Set
open scoped BigOperators


theorem algebra_9067 {f : ℝ → ℝ} (hf : f = λ x => (sin x + cos x)^2) :
    IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (Real.pi) :=
by
  constructor
  · -- Show that π is a positive period
    constructor
    · -- Show that π > 0
      exact Real.pi_pos
    · -- Show that f = λ x, f (x + π)
      funext x
      rw [hf]
      simp [sin_add_pi, cos_add_pi]
      <;> nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq (x + Real.pi)]
  · -- Show that π is the least positive period
    intro T ⟨hT_pos, h_eq⟩
    by_contra h
    push_neg at h
    have h1 := congr_fun h_eq (Real.pi / 2 - T / 2)
    simp [hf] at h1
    have h2 : sin (Real.pi / 2 - T / 2) = cos (T / 2) := by
      rw [show Real.pi / 2 - T / 2 = Real.pi / 2 - T / 2 by ring]
      rw [sin_pi_div_two_sub]
    have h3 : cos (Real.pi / 2 - T / 2) = sin (T / 2) := by
      rw [show Real.pi / 2 - T / 2 = Real.pi / 2 - T / 2 by ring]
      rw [cos_pi_div_two_sub]
    have h4 : sin (Real.pi / 2 - T / 2 + T) = cos (T / 2) := by
      have h3 : Real.pi / 2 - T / 2 + T = Real.pi / 2 + T / 2 := by ring
      rw [h3]
      have h4 : sin (Real.pi / 2 + T / 2) = cos (T / 2) := by
        rw [sin_add]
        simp [sin_pi_div_two, cos_pi_div_two]
        all_goals ring_nf <;> simp [Real.sin_pi_div_two]
      linarith [h4]
    have h5 : cos (Real.pi / 2 - T / 2 + T) = - sin (T / 2) := by
      have h3 : Real.pi / 2 - T / 2 + T = Real.pi / 2 + T / 2 := by ring
      rw [h3]
      have h4 : cos (Real.pi / 2 + T / 2) = - sin (T / 2) := by
        rw [cos_add]
        simp [sin_pi_div_two, cos_pi_div_two]
        all_goals ring_nf <;> simp [Real.sin_pi_div_two]
      linarith [h4]
    simp [h2, h3, h4, h5] at h1
    have h6 : sin (T / 2) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith
      linarith [Real.pi_pos, h]
    have h7 : cos (T / 2) = 0 := by
      have h_eq' : (cos (T / 2) + sin (T / 2)) ^ 2 = (cos (T / 2) - sin (T / 2)) ^ 2 := h1
      ring_nf at h_eq' 
      have h8 : cos (T / 2) * sin (T / 2) = 0 := by
        nlinarith [Real.sin_sq_add_cos_sq (T / 2)]
      cases mul_eq_zero.mp h8 with 
      | inl h9 => 
        linarith 
      | inr h9 => 
        nlinarith [h6, h9]
    have h8 : 0 < T / 2 := by 
      linarith [hT_pos] 
    have h9 : T / 2 < Real.pi / 2 := by 
      linarith [Real.pi_pos, h] 
    have h10 : cos (T / 2) > 0 := by 
      apply cos_pos_of_mem_Ioo 
      constructor <;> linarith [h8, h9, Real.pi_pos] 
    linarith [h7, h10]