import Mathlib

theorem other_252543 (d u f : ℝ) (h₀ : d > 0) (h₁ : u > 0) (h₂ : f > 0)
    (h₃ : d / u = d / f) (h₄ : u / f = 2 * (d / u)) :
    f / d = 2 := by 
  have h6 : d ≠ 0 := by linarith
  have h7 : u ≠ 0 := by linarith
  have h8 : f ≠ 0 := by linarith
  have h₅ : f = u := by
    field_simp [h6, h7, h8] at h₃
    nlinarith -- This yields f = u
  have h12 : u = 2 * d := by 
    have h11 : u ≠ 0 := by linarith
    rw [show f = u by linarith [h₅]] at h₄ 
    field_simp [h11] at h₄
    nlinarith 
  have h13 : f = 2 * d := by 
    linarith [h₅, h12]
  have h14 : d ≠ 0 := by linarith
  rw [show f = 2 * d by linarith [h13]]
  field_simp [h14]
  <;> nlinarith