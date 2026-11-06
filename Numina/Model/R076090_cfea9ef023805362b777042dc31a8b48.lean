import Mathlib

theorem algebra_48221 {x y z a : ℝ} (h₀ : x + y + z = a) (h₁ : x^2 + y^2 + z^2 = a^2)
    (h₂ : x^3 + y^3 + z^3 = a^3) :
    (x, y, z) = (a, 0, 0) ∨ (x, y, z) = (0, a, 0) ∨ (x, y, z) = (0, 0, a) := by
  have h3 : x * y + x * z + y * z = 0 := by
    have h4 : (x + y + z)^2 = x^2 + y^2 + z^2 + 2 * (x * y + x * z + y * z) := by ring
    rw [h₀, h₁] at h4
    nlinarith
  have h4 : x * y * z = 0 := by
    have h5 : x^3 + y^3 + z^3 - 3 * (x * y * z) = (x + y + z) * (x^2 + y^2 + z^2 - (x * y + x * z + y * z)) := by ring 
    rw [h₀, h₁, h3] at h5
    have h6 : x^3 + y^3 + z^3 - 3 * (x * y * z) = a^3 := by nlinarith 
    have h7 : 3 * (x * y * z) = 0 := by nlinarith [h₂, h6] 
    have h8 : x * y * z = 0 := by linarith 
    exact h8 
  cases' (mul_eq_zero.mp h4) with h5 h6 
  · cases' (mul_eq_zero.mp h5) with h7 h8 
    · -- case where x = 0 
      have hx : x = 0 := by linarith 
      have h01 : y + z = a := by linarith [h₀, hx]
      have h02 : y * z = 0 := by 
        rw [hx] at h3 
        nlinarith 
      cases' (mul_eq_zero.mp h02) with h11 h12 
      · -- case where y = 0 
        have hy : y = 0 := by linarith 
        have hz : z = a := by linarith [h01, hy] 
        simp [hx, hy, hz]
      · -- case where z = 0 
        have hz : z = 0 := by linarith 
        have hy : y = a := by linarith [h01, hz] 
        simp [hx, hy, hz]
    · -- case where y = 0 
      have hy : y = 0 := by linarith 
      have h01 : x + z = a := by linarith [h₀, hy] 
      have h02 : x * z = 0 := by 
        rw [hy] at h3 
        nlinarith 
      cases' (mul_eq_zero.mp h02) with h21 h22 
      · -- case where x = 0 
        have hx : x = 0 := by linarith 
        have hz : z = a := by linarith [h01, hx] 
        simp [hx, hy, hz]
      · -- case where z = 0 
        have hz : z = 0 := by linarith 
        have hx : x = a := by linarith [h01, hz] 
        simp [hx, hy, hz]
  · -- case where z = 0 
    have hz : z = 0 := by linarith 
    have h01 : x + y = a := by linarith [h₀, hz] 
    have h02 : x * y = 0 := by 
      rw [hz] at h3 
      nlinarith 
    cases' (mul_eq_zero.mp h02) with h31 h32 
    · -- case where x = 0 
      have hx : x = 0 := by linarith 
      have hy : y = a := by linarith [h01, hx] 
      simp [hx, hy, hz]
    · -- case where y = 0 
      have hy : y = 0 := by linarith 
      have hx : x = a := by linarith [h01, hy] 
      simp [hx, hy, hz]