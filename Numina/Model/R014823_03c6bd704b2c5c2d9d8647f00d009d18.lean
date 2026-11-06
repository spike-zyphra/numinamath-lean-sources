import Mathlib

theorem algebra_238107 (a : ℕ → ℕ) (h₀ : a 2 = a 0 + a 1) (h₁ : a 3 = a 1 + a 2)
    (h₂ : a 4 = a 2 + a 3) (h₃ : a 5 = a 3 + a 4) (h₄ : a 4 = 7) :
    a 0 = 2 ∧ a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 4 ∧ a 4 = 7 ∧ a 5 = 11 := by 
  have eq6 : a 4 = 2 * a 0 + 3 * a 1 := by 
    rw [h₂]
    rw [h₀] at *
    rw [h₁]
    all_goals omega
  have h5 : 2 * a 0 + 3 * a 1 = 7 := by
    omega
  have ha0 : a 0 = 2 := by
    omega
  have ha1 : a 1 = 1 := by
    omega
  have ha2 : a 2 = 3 := by 
    simp [ha0, ha1] at h₀ ⊢
    omega
  have ha3 : a 3 = 4 := by
    simp [ha1, ha2] at h₁ ⊢
    omega
  have ha4 : a 4 = 7 := by 
    omega
  have ha5 : a 5 = 11 := by
    simp [ha3, ha4] at h₃ ⊢
    omega
  exact ⟨ha0, ha1, ha2, ha3, ha4, ha5⟩