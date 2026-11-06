import Mathlib

theorem algebra_197595 (x y z : ℝ) (h₀ : x + y * z = 7) (h₁ : x * y + z = 5) (h₂ : x + y + z = 6) :
    (x = 1 ∧ y = 2 ∧ z = 3) ∨ (x = 1 ∧ y = 3 ∧ z = 2) := by
  have hz : z = 6 - x - y := by linarith [h₂]
  rw [hz] at h₁ 
  have h3 : (x - 1) * (y - 1) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp h3) with hx hy 
  · -- Case that x = 1. 
    have hx1 : x = 1 := by linarith 
    have eq1 : y + z = 5 := by 
      rw [hx1] at h₂ 
      linarith 
    have eq2 : y * z = 6 := by 
      rw [hx1] at h₀ 
      nlinarith 
    have hy_eq : y = 2 ∨ y = 3 := by
      have hquad : y^2 - 5*y + 6 = 0 := by 
        have hz_eq : z = 5 - y := by linarith [eq1]
        rw [hz_eq] at eq2 
        nlinarith 
      have factored : (y - 2) * (y - 3) = 0 := by 
        linarith [hquad] 
      cases' (mul_eq_zero.mp factored) with hy1 hy2 
      · -- y - 2 = 0 therefore y = 2
        left 
        linarith 
      · -- y - 3 = 0 therefore y = 3
        right 
        linarith 
    cases' hy_eq with hy2 hy3
    · -- y = 2 
      have hz3 : z = 3 := by 
        have hz_eq : z = 5 - y := by linarith [eq1]
        rw [show y = 2 by linarith [hy2] ] at hz_eq 
        linarith 
      left 
      exact ⟨hx1, by linarith, by linarith⟩ 
    · -- y = 3 
      have hz2 : z = 2 := by 
        have hz_eq : z = 5 - y := by linarith [eq1]
        rw [show y = 3 by linarith [hy3] ] at hz_eq 
        linarith 
      right 
      exact ⟨hx1, by linarith, by linarith⟩ 
  · -- Case that y = 1. 
    have hy1 : y = 1 := by linarith 
    rw [hy1] at h₀ h₂ 
    have h3 : x + z = 7 := by
      nlinarith 
    have h4 : x + z = 5 := by 
      linarith 
    linarith