import Mathlib

theorem algebra_160816 (p v k : ℝ) (h₀ : p + v + k ≥ 8.5) (h₁ : p + v + k ≤ 8.5)
    (h₂ : p + v = 5) (h₃ : p + k = 6.5) (h₄ : k + v = 5.5) :
    p = 3 ∧ v = 2 ∧ k = 3.5 := by
  have h5 : p + v + k = 8.5 := by 
    linarith
  have hk : k = 3.5 := by 
    linarith [h₂, h5]
  have hp : p = 3 := by 
    rw [hk] at h₃
    linarith
  have hv : v = 2 := by 
    rw [hp] at h₂
    linarith
  exact ⟨hp, hv, hk⟩