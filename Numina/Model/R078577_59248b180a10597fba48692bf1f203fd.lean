import Mathlib

theorem algebra_320427 {a b c : ℝ} (h₀ : a + b + c = 1) (h₁ : a ^ 2 + b ^ 2 + c ^ 2 = 2)
    (h₂ : a ^ 3 + b ^ 3 + c ^ 3 = 3) :
    a * b * c = 1 / 6 ∧ a ^ 4 + b ^ 4 + c ^ 4 = 25 / 6 := by 
  have h₃ : a * b + b * c + c * a = -1 / 2 := by
    have h : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by ring
    rw [h₀, h₁] at h 
    linarith 
  have habc : a * b * c = 1 / 6 := by 
    have h : a ^ 3 + b ^ 3 + c ^ 3 = (a + b + c) ^ 3 - 3 * (a + b + c) * (a * b + b * c + c * a) + 3 * (a * b * c) := by ring
    rw [h₀, h₃] at h 
    rw [h₂] at h 
    linarith 
  have h₄ : a ^ 4 + b ^ 4 + c ^ 4 = 25 / 6 := by 
    have h₅ : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 = a ^ 4 + b ^ 4 + c ^ 4 + 2 * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2) := by ring 
    rw [h₁] at h₅ 
    have h₆ : a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 = -1 / 12 := by 
      have h₇ : (a * b + b * c + c * a) ^ 2 = a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 + 2 * (a * b * c) * (a + b + c) := by ring
      rw [h₃, habc, h₀] at h₇ 
      linarith 
    linarith 
  exact ⟨habc, h₄⟩