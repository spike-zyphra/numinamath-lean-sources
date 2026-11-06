import Mathlib

theorem algebra_303871 (a b c : ℝ) (h₀ : a + b + c = 0) (h₁ : a > b ∧ b > c) :
    -2 < c / a ∧ c / a < -1 / 2 := by
  have h2 : a > 0 := by
    nlinarith [h₀, h₁.1, h₁.2]

  have h3 : b = -a - c := by
    linarith

  have h4 : a > b := h₁.1
  have h5 : b > c := h₁.2

  have h6 : -2 < c / a := by
    have h7 : a > b := h₁.1
    rw [show b = -a - c by linarith] at h7
    have h8 : 2 * a > -c := by linarith
    have h9 : c / a > -2 := by
      apply (lt_div_iff₀ (by linarith)).mpr
      linarith
    linarith
  
  have h10 : c / a < -1 / 2 := by 
    have h11 : b > c := h₁.2
    rw [show b = -a - c by linarith] at h11
    have h12 : -a > 2 * c := by linarith
    have h13 : c / a < -1 / 2 := by
      apply (div_lt_iff₀ (by linarith)).mpr
      linarith
    linarith
  
  constructor
  · -- Proof of -2 < c / a
    linarith [h6]
  · -- Proof of c / a < -1 / 2
    linarith [h10]