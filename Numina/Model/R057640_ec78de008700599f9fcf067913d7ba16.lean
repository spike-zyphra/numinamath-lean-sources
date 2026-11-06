import Mathlib

theorem algebra_239688 (x y z : ℕ) (h₀ : x + y + z = 300) (h₁ : x = 2 * y) (h₂ : z = x + y) :
    x = 100 ∧ y = 50 ∧ z = 150 := by 
  have h3 : z = 3 * y := by 
    rw [h₁] at h₂ 
    omega 
  have hy : y = 50 := by 
    rw [h₁, h3] at h₀ 
    omega 
  have hx : x = 100 := by 
    rw [hy] at h₁ 
    omega 
  have hz : z = 150 := by 
    rw [hy] at h3 
    omega 
  exact ⟨hx, hy, hz⟩