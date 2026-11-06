import Mathlib

theorem algebra_170111 (p : Fin 3 → ℝ) (h₀ : p 0 + p 1 + p 2 = 1)
    (h₁ : ∑ x in Finset.range 3, (x + 1) * p x = 2.3) (h₂ : ∑ x in Finset.range 3, (x + 1)^2 * p x = 5.9) :
    p 0 = 0.2 ∧ p 1 = 0.3 ∧ p 2 = 0.5 := by

  have eq1 : ∑ x in Finset.range 3, (x + 1) * p x = p 0 + 2 * p 1 + 3 * p 2 := by 
    simp [Finset.sum_range_succ]
    <;> ring

  have eq2 : ∑ x in Finset.range 3, (x + 1)^2 * p x = p 0 + 4 * p 1 + 9 * p 2 := by 
    simp [Finset.sum_range_succ]
    <;> ring
  
  rw [eq1] at h₁
  rw [eq2] at h₂
  
  have eq4 : p 2 = (0.5 : ℝ) := by
    norm_num at h₁ h₂ h₀ ⊢
    linarith
  
  have eq5 : p 1 = (0.3 : ℝ) := by
    norm_num at h₁ h₂ h₀ eq4 ⊢
    linarith
  
  have eq6 : p 0 = (0.2 : ℝ) := by
    norm_num at h₁ h₂ h₀ eq5 eq4 ⊢
    linarith
  
  exact ⟨eq6, eq5, eq4⟩