import Mathlib

theorem algebra_259510 {a r : ℚ} (ha : a ≠ 0) (hr : r ≠ 0)
    (h : ∃ d, a + 20 = d * r ∧ a + 50 = d * r ^ 2 ∧ a + 100 = d * r ^ 3) :
    r = 5 / 3 := by
  rcases h with ⟨d, h₁, h₂, h₃⟩
  have h4 : d ≠ 0 := by
    by_contra h4
    rw [h4] at h₁ h₂ h₃
    have h₁' : a + 20 = (0 : ℚ) := by linarith
    have h₂' : a + 50 = (0 : ℚ) := by linarith
    have ha_eq1 : a = -20 := by linarith
    have ha_eq2 : a = -50 := by linarith
    linarith
  have h5 : d * r * (r - 1) = 30 := by
    have h₁' : a + 20 = d * r := by linarith
    have h₂' : a + 50 = d * r^2 := by linarith
    -- Calculate (a + 50) - (a + 20) = d * r^2 - d * r
    have : (a + 50) - (a + 20) = d * r^2 - d * r := by
      rw [h₂', h₁']
    -- Simplifies to 30 = d * r * (r - 1)
    have : d * r * (r - 1) = 30 := by linarith
    linarith
  have h6 : d * r^2 * (r - 1) = 50 := by
    have h₂' : a + 50 = d * r^2 := by linarith
    have h₃' : a + 100 = d * r^3 := by linarith
    -- Calculate (a + 100) - (a + 50) = d * r^3 - d * r^2
    have : (a + 100) - (a + 50) = d * r^3 - d * r^2 := by
      rw [h₃', h₂']
    -- Simplifies to 50 = d * r^2 * (r - 1)
    have : d * r^2 * (r - 1) = 50 := by linarith
    linarith
  have eq2 : d * r * (r - 1) ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    exact h4
    exact hr
    by_contra h5'
    have hr_eq1 : r = 1 := by linarith
    rw [hr_eq1] at h5
    -- Then h5 would be 0 = 30, contradiction
    linarith
  have : r = 5 / 3 := by
    apply (mul_left_inj' eq2).mp
    -- Now, $d \cdot r^2 \cdot (r - 1) - (d \cdot r \cdot (r - 1)) * r = 0$
    linarith
  linarith