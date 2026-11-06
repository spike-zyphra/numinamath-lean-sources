import Mathlib

theorem algebra_110134 (x y : ℝ) (h₀ : Real.sin x * Real.cos y = 1 / 2) (h₁ : Real.cos x * Real.sin y = 1 / 2) :
    Real.cos (2 * x) - Real.sin (2 * y) = 1 ∨ Real.cos (2 * x) - Real.sin (2 * y) = -1 := by
  have h2 : Real.sin (x + y) = 1 := by
    have h3 : Real.sin (x + y) = Real.sin x * Real.cos y + Real.cos x * Real.sin y := by
      rw [Real.sin_add]
    rw [h3]
    linarith [h₀, h₁]
  have h3 : Real.sin (x - y) = 0 := by
    have h4 : Real.sin (x - y) = Real.sin x * Real.cos y - Real.cos x * Real.sin y := by
      rw [Real.sin_sub]
    rw [h4]
    linarith [h₀, h₁]
  have h9 : Real.cos (x + y) = 0 := by
    have h8' : Real.sin (x + y) ^ 2 + Real.cos (x + y) ^ 2 = 1 := Real.sin_sq_add_cos_sq (x + y)
    rw [h2] at h8'
    nlinarith
  have h13 : Real.cos (x - y) ^ 2 = 1 := by
    have h14 : Real.sin (x - y) = 0 := h3
    have h15 : Real.sin (x - y) ^ 2 + Real.cos (x - y) ^ 2 = 1 := Real.sin_sq_add_cos_sq (x - y)
    rw [h14] at h15
    nlinarith
  have h10 : Real.cos (2 * x) = 0 := by
    have h11 : Real.cos (2 * x) = Real.cos (x + y) * Real.cos (x - y) - Real.sin (x + y) * Real.sin (x - y) := by
      rw [show 2 * x = (x + y) + (x - y) by ring]
      rw [Real.cos_add]
    rw [h11]
    have h14 : Real.cos (x + y) = 0 := h9
    have h15 : Real.sin (x + y) = 1 := h2
    have h16 : Real.sin (x - y) = 0 := h3
    rw [h14, h15, h16]
    norm_num
  have h16 : Real.cos (2 * y) = 0 := by
    have h16 : Real.cos (2 * y) = Real.cos (x + y) * Real.cos (x - y) + Real.sin (x + y) * Real.sin (x - y) := by
      have h17 : 2 * y = (x + y) - (x - y) := by ring
      rw [h17]
      rw [Real.cos_sub]
    rw [h16]
    have h14 : Real.cos (x + y) = 0 := h9
    have h15 : Real.sin (x + y) = 1 := h2
    have h16 : Real.sin (x - y) = 0 := h3
    rw [h14, h15, h16]
    norm_num
  have h17 : Real.sin (2 * y) ^ 2 = 1 := by
    have h18 : Real.sin (2 * y) ^ 2 + Real.cos (2 * y) ^ 2 = 1 := Real.sin_sq_add_cos_sq (2 * y)
    rw [h16] at h18
    nlinarith
  have h18 : Real.sin (2 * y) = 1 ∨ Real.sin (2 * y) = -1 := by
    have h17' : Real.sin (2 * y) ^ 2 = 1 := h17
    rw [sq_eq_one_iff] at h17'
    tauto
  rcases h18 with (h | h)
  · -- Real.sin (2 * y) = 1
    have h20 : Real.cos (2 * x) - Real.sin (2 * y) = -1 := by
      have h21 : Real.sin (2 * y) = 1 := h
      have h22 : Real.cos (2 * x) = 0 := h10
      linarith
    right
    linarith
  · -- Real.sin (2 * y) = -1
    have h20 : Real.cos (2 * x) - Real.sin (2 * y) = 1 := by
      have h21 : Real.sin (2 * y) = -1 := h
      have h22 : Real.cos (2 * x) = 0 := h10
      linarith
    left
    linarith