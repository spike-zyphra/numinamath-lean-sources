import Mathlib

theorem algebra_118781 {x y z : ℝ} (h₀ : (x + y) * (x + y + z) = 18) (h₁ : (y + z) * (x + y + z) = 30) (h₂ : (z + x) * (x + y + z) = 24) :
    (x = 1 ∧ y = 2 ∧ z = 3) ∨ (x = -1 ∧ y = -2 ∧ z = -3) := by
  have eq4 : (x + y + z) ^ 2 - (x + y + z) * z = 18 := by
    have h4 : (x + y) = (x + y + z) - z := by ring
    rw [h4] at h₀
    linarith
  have eq5 : (x + y + z) ^ 2 - (x + y + z) * x = 30 := by
    have h5 : (y + z) = (x + y + z) - x := by ring
    rw [h5] at h₁
    linarith
  have eq6 : (x + y + z) ^ 2 - (x + y + z) * y = 24 := by
    have h6 : (z + x) = (x + y + z) - y := by ring
    rw [h6] at h₂
    linarith
  have eq7 : (x + y + z) ^ 2 = 36 := by
    nlinarith
  have hS : (x + y + z) = 6 ∨ (x + y + z) = -6 := by
    have h4 : (x + y + z) ^ 2 - 36 = 0 := by nlinarith
    have h5 : ((x + y + z) - 6) * ((x + y + z) + 6) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · left
      linarith
    · right
      linarith
  cases' hS with hS hS
  · -- Case where x + y + z = 6
    have h3 : x + y = 3 := by
      have h4 : (x + y) * (x + y + z) = 18 := h₀
      rw [show x + y + z = 6 by linarith [hS]] at h4
      nlinarith
    have h4 : y + z = 5 := by
      have h5 : (y + z) * (x + y + z) = 30 := h₁
      rw [show x + y + z = 6 by linarith [hS]] at h5
      nlinarith
    have h5 : z + x = 4 := by
      have h6 : (z + x) * (x + y + z) = 24 := h₂
      rw [show x + y + z = 6 by linarith [hS]] at h6
      nlinarith
    have hx : x = 1 := by
      nlinarith [hS, h3, h4, h5]
    have hy : y = 2 := by
      nlinarith [h3, hx]
    have hz : z = 3 := by
      nlinarith [hS, h3, h4, h5]
    left
    exact ⟨hx, hy, hz⟩
  · -- Case where x + y + z = -6
    have h3 : x + y = -3 := by
      have h4 : (x + y) * (x + y + z) = 18 := h₀
      rw [show x + y + z = -6 by linarith [hS]] at h4
      nlinarith
    have h4 : y + z = -5 := by
      have h5 : (y + z) * (x + y + z) = 30 := h₁
      rw [show x + y + z = -6 by linarith [hS]] at h5
      nlinarith
    have h5 : z + x = -4 := by
      have h6 : (z + x) * (x + y + z) = 24 := h₂
      rw [show x + y + z = -6 by linarith [hS]] at h6
      nlinarith
    have hx : x = -1 := by
      nlinarith [hS, h3, h4, h5]
    have hy : y = -2 := by
      nlinarith [h3, hx]
    have hz : z = -3 := by
      nlinarith [hS, h3, h4, h5]
    right
    exact ⟨hx, hy, hz⟩