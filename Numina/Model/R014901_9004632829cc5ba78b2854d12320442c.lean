import Mathlib

theorem algebra_135946 {x y z : ℝ} (h₀ : (x + 1) * y * z = 12) (h₁ : (y + 1) * z * x = 4)
    (h₂ : (z + 1) * x * y = 4) :
    (x = 2 ∧ y = -2 ∧ z = -2) ∨ (x = 1 / 3 ∧ y = 3 ∧ z = 3) := by 
  have h3 : (y + 1) * z * x = (z + 1) * x * y := by linarith [h₁, h₂]
  by_cases hx : x = 0
  · -- If x = 0, then from equation h₁ : (y + 1) * z * 0 = 0 = 4. Contradiction.
    rw [hx] at h₁ h₂
    nlinarith 
  · -- x ≠ 0
    have h4 : (y + 1) * z = (z + 1) * y := by 
      apply (mul_left_inj' hx).mp 
      linarith
    have h5 : z = y := by 
      nlinarith 
    rw [show z = y by linarith] at h₀ h₁ h₂ 
    have h11 : y = -2 ∨ y = 3 := by
      have h7 : (x + 1) * y^2 = 12 := by
        linarith 
      have h8 : x * y * (y + 1) = 4 := by
        nlinarith
      have h9 : (y + 2)^2 * (y - 3) = 0 := by 
        nlinarith [sq_nonneg (y + 2), sq_nonneg (x * y), sq_nonneg (y^2), sq_pos_of_ne_zero (show y ≠ 0 by 
          by_contra h 
          rw [h] at h8 h7
          nlinarith
        ), sq_nonneg (x * (y + 1)), sq_nonneg (x)]
      cases' (mul_eq_zero.mp h9) with h10 h11
      · -- (y+2)^2 =0 
        have h12 : y + 2 = 0 := by 
          apply pow_eq_zero 
          exact h10
        left
        linarith 
      · -- y-3=0 
        right 
        linarith 
    cases' h11 with hy1 hy2
    · -- y = -2
      have hy2 : y = -2 := by 
        linarith 
      have hz2 : z = -2 := by 
        nlinarith [hy2, show z = y by linarith] 
      have hx2 : x = 2 := by 
        -- From (x+1)y^2 =12, set y=-2, get (x+1)4=12 → x+1=3 → x=2
        have h0' : (x + 1) * y^2 = 12 := by
          nlinarith 
        rw [hy2] at h0'
        nlinarith 
      left 
      exact ⟨hx2, hy2, hz2⟩ 
    · -- y = 3
      have hy3 : y = 3 := by 
        linarith 
      have hz3 : z = 3 := by 
        nlinarith [hy3, show z = y by linarith] 
      have hx3 : x = 1 / 3 := by 
        -- From (x+1)y^2 =12, set y=3, get (x+1)9=12 → x+1=4/3 → x=1/3
        have h0' : (x + 1) * y^2 = 12 := by
          nlinarith 
        rw [hy3] at h0'
        nlinarith 
      right 
      exact ⟨hx3, hy3, hz3⟩