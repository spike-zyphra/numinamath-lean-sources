import Mathlib

theorem algebra_202745 {a : ℝ} (f : ℝ → ℝ) (hf : f = fun x => (x + a) / (x ^ 2 + 1 / 2))
    (hmax : ∃ x, f x = 1 / 2) (hmin : ∃ x, f x = -1) :
    f 0 = -1 / 2 := by 
  rcases hmax with ⟨x₁, h₁⟩ 
  rcases hmin with ⟨x₂, h₂⟩ 
  have eq1 : (x₁ + a) / (x₁ ^ 2 + 1 / 2) = 1 / 2 := by 
    rw [hf] at h₁ 
    simpa using h₁ 
  have eq2 : (x₂ + a) / (x₂ ^ 2 + 1 / 2) = -1 := by 
    rw [hf] at h₂ 
    simpa using h₂ 
  have eq3 : x₁ ^ 2 - 2 * x₁ - 2 * a + 1 / 2 = 0 := by 
    have hne : x₁ ^ 2 + 1 / 2 > 0 := by 
      nlinarith [sq_nonneg x₁] 
    have eq1' : (x₁ + a) / (x₁ ^ 2 + 1 / 2) = 1 / 2 := eq1 
    have eq4 : 2 * (x₁ + a) = x₁ ^ 2 + 1 / 2 := by 
      field_simp at eq1' ⊢ 
      nlinarith 
    nlinarith
  -- Convert eq2 into a polynomial equation
  have eq4 : x₂ ^ 2 + x₂ + a + 1 / 2 = 0 := by
    have hne : x₂ ^ 2 + 1 / 2 > 0 := by
      nlinarith [sq_nonneg x₂]
    have eq2' : (x₂ + a) / (x₂ ^ 2 + 1 / 2) = -1 := eq2
    have eq5 : x₂ + a = - (x₂ ^ 2 + 1 / 2) := by
      field_simp at eq2' ⊢
      nlinarith 
    nlinarith
  have ha : a = -1 / 4 := by 
    nlinarith [sq_nonneg (x₁ - 1), sq_nonneg (x₂ + 1 / 2), sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ - 1)]
  have h3 : f 0 = (0 + a) / (0 ^ 2 + 1 / 2) := by 
    simp [hf]
  rw [h3]
  rw [ha]
  norm_num