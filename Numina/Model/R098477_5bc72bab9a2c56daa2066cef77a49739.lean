import Mathlib

theorem algebra_317587 {a b c : ℝ} (h₀ : a * b * c ≠ 0) (h₁ : a + b + c = 0) :
    a ^ 2 / (b * c) + b ^ 2 / (a * c) + c ^ 2 / (a * b) = 3 := by 
  have ha : a ≠ 0 := by 
    by_contra h
    have : a * b * c = 0 := by 
      rw [h]
      all_goals ring
    contradiction
  have hb : b ≠ 0 := by 
    by_contra h
    have : a * b * c = 0 := by 
      rw [h]
      all_goals ring
    contradiction
  have hc : c ≠ 0 := by 
    by_contra h
    have : a * b * c = 0 := by 
      rw [h]
      all_goals ring
    contradiction

  have h3 : a ^ 3 + b ^ 3 + c ^ 3 = 3 * (a * b * c) := by 
    have h₂ : a + b + c = 0 := h₁ 
    have h4 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + a * c + b * c)) := by 
      ring 
    rw [h₂] at h4 
    have h5 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = 0 := by 
      linarith 
    linarith 

  have eq1 : a ^ 2 / (b * c) + b ^ 2 / (a * c) + c ^ 2 / (a * b) = (a ^ 3 + b ^ 3 + c ^ 3) / (a * b * c) := by 
    field_simp [hb, hc, ha, show a * c ≠ 0 by 
      apply mul_ne_zero 
      exact ha 
      exact hc 
      , show b * c ≠ 0 by 
        apply mul_ne_zero 
        exact hb 
        exact hc 
        , show a * b ≠ 0 by 
          apply mul_ne_zero 
          exact ha 
          exact hb 
          ]
    <;> ring_nf <;> field_simp <;> ring

  rw [eq1] 
  rw [h3]
  field_simp [h₀]
  all_goals linarith