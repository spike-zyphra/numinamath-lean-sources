import Mathlib

theorem algebra_259826 (x y z : ℝ) (h₁ : x + y + z > 0) (h₂ : x * y + y * z + z * x > 0)
    (h₃ : x * y * z > 0) :
    x > 0 ∧ y > 0 ∧ z > 0 := by
  have h4 : x > 0 := by
    by_contra hx
    push_neg at hx
    have h5 : x ≤ 0 := by linarith
    by_cases h6 : x < 0
    · -- x < 0, so product x * y * z >0, so y * z < 0
      have h7 : y * z < 0 := by
        nlinarith [h₃, h6]
      -- Then need to derive contradiction from h₂ and h7.
      -- h₂: x * y + y * z + z * x >0, but x <0
      nlinarith [sq_nonneg (y + z), sq_nonneg (x), sq_nonneg (y - z), sq_nonneg (x + y + z)]
    · -- x = 0, which contradicts h₃
      have h7 : x = 0 := by linarith
      rw [h7] at h₃
      nlinarith
  have h5 : y > 0 := by
    by_contra hy
    push_neg at hy
    have h6 : y ≤ 0 := by linarith
    by_cases h7 : y < 0
    · -- y < 0
      have h8 : x * z < 0 := by
        have h8 : x * y * z > 0 := h₃
        have : x * (y * z) > 0 := by nlinarith
        nlinarith [h7]
      nlinarith [sq_nonneg (x + z), sq_nonneg (y), sq_nonneg (x - z), sq_nonneg (x + y + z)]
    · -- y = 0
      have h8 : y = 0 := by linarith
      rw [h8] at h₃
      nlinarith
  have h6 : z > 0 := by
    by_contra hz
    push_neg at hz
    have h7 : z ≤ 0 := by linarith
    by_cases h8 : z < 0
    · -- z < 0
      have h9 : x * y < 0 := by
        have h9 : x * y * z > 0 := h₃
        have : (x * y) * z > 0 := by nlinarith
        nlinarith [h8]
      nlinarith [sq_nonneg (x + y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x + y + z)]
    · -- z = 0
      have h9 : z = 0 := by linarith
      rw [h9] at h₃
      nlinarith
  exact ⟨h4, h5, h6⟩