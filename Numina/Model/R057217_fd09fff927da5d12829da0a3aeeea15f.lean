import Mathlib

theorem algebra_302137 (a b c : ℝ) (h₀ : a > b) (h₁ : b > c)
    (h₂ : a + b + c = 0) :
    c / a ∈ Set.Ioo (-2) (-1 / 2) := by
  have h3 : a + b + c = 0 := h₂
  have h4 : b = -a - c := by 
    linarith
  have h5 : a > -a - c := by linarith [h₀, h4]
  have h6 : -a - c > c := by linarith [h₁, h4]
  have ha : a ≠ 0 := by
    by_contra h
    rw [h] at h₂
    nlinarith

  have h_a_pos : a > 0 := by
    by_contra h
    push_neg at h
    -- Assume a ≤ 0
    have h8 : a ≤ 0 := by linarith
    -- b + c = -a from h₂
    have h7 : b + c = -a := by linarith
    nlinarith

  have hc1 : c / a > -2 := by
    apply (lt_div_iff' (by linarith)).mpr
    --tra
    nlinarith
  have hc2 : c / a < -1 / 2 := by
    apply (div_lt_iff' (by linarith)).mpr
    --tra
    nlinarith
  exact ⟨hc1, hc2⟩