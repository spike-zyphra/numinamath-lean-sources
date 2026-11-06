import Mathlib

theorem algebra_267866 {x y z : ℝ} (h₀ : x^2 - y = z^2) (h₁ : y^2 - z = x^2) (h₂ : z^2 - x = y^2) :
    (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = 1 ∧ y = 0 ∧ z = -1) ∨ (x = 0 ∧ y = -1 ∧ z = 1) ∨ (x = -1 ∧ y = 1 ∧ z = 0) := by 
  have h3 : x + y + z = 0 := by
    nlinarith
  have h4 : z = -x - y := by linarith 
  rw [h4] at h₀
  have h5 : y * (y + 2 * x + 1) = 0 := by 
    nlinarith
  cases' (mul_eq_zero.mp h5) with hy1 hy2
  · -- Case y = 0 
    have hy : y = 0 := by linarith 
    have h41 : z = -x := by 
      linarith [h4, hy] 
    have h6 : x * (x - 1) = 0 := by 
      rw [hy, h41] at h₁ 
      nlinarith 
    cases' (mul_eq_zero.mp h6) with hx1 hx2 
    · -- Case x = 0 
      have hx : x = 0 := by linarith 
      have hz : z = 0 := by 
        linarith [h41, hx] 
      left 
      exact ⟨hx, hy, hz⟩ 
    · -- Case x - 1 = 0 
      have hx : x = 1 := by linarith 
      have hz : z = -1 := by 
        linarith [h41, hx] 
      right 
      left 
      exact ⟨hx, hy, hz⟩ 
  · -- Case y + 2x + 1 = 0 
    have hy : y = -2 * x - 1 := by linarith 
    have h42 : z = x + 1 := by 
      rw [hy] at h4 
      nlinarith 
    rw [hy, h42] at h₁ 
    have h7 : 3 * x * (x + 1) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h7) with hx1 hx2 
    · -- Case 3 * x = 0 
      have hx : x = 0 := by linarith 
      have hy' : y = -1 := by 
        rw [hx] at hy 
        linarith 
      have hz : z = 1 := by 
        rw [hx] at h42 
        linarith 
      right 
      right 
      left 
      exact ⟨hx, hy', hz⟩ 
    · -- Case x + 1 = 0 
      have hx : x = -1 := by linarith 
      have hy' : y = 1 := by 
        rw [hx] at hy 
        linarith 
      have hz : z = 0 := by 
        rw [hx] at h42 
        linarith 
      right 
      right 
      right 
      exact ⟨hx, hy', hz⟩