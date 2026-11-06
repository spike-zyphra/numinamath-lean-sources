import Mathlib

open Real
theorem algebra_212567 (a b c d : ℝ)  (h₆ : logb a b = 15) (h₇ : logb a c = 20) (h₉ : logb b c = 28) :
    logb b d = 28 ∨ logb c d = 420 := by 
  have h1 : log b / log a = 15 := by 
    have h11 : logb a b = log b / log a := by 
      field_simp [logb]
    rw [h11] at h₆ 
    linarith 
  have h2 : log c / log a = 20 := by 
    have h12 : logb a c = log c / log a := by 
      field_simp [logb]
    rw [h12] at h₇ 
    linarith 
  have h3 : log c / log b = 28 := by 
    have h13 : logb b c = log c / log b := by 
      field_simp [logb]
    rw [h13] at h₉ 
    linarith 
  by_cases h4 : log a = 0 
  · -- case log a = 0
    rw [h4] at h1 h2 
    field_simp at h1 h2 
    all_goals linarith 
  · -- case log a ≠ 0 
    have h5 : log c = 420 * log a := by
      have h6 : log c = 28 * log b := by 
        have h66 : log c / log b = 28 := h3 
        have h77 : log b ≠ 0 := by 
          by_contra h
          rw [h] at h1 h3 
          field_simp [h4] at h1 h3 
          all_goals linarith 
        field_simp [h77] at h3 ⊢
        linarith 
      have h7 : log b = 15 * log a := by 
        have h11 : log b / log a = 15 := h1 
        have h88 : log a ≠ 0 := by
          exact_mod_cast h4 
        field_simp [h88] at h11 ⊢ 
        linarith 
      rw [h6, h7] 
      all_goals ring 
    have h66 : log a = 0 := by
      have h44 : log c / log a = 20 := h2 
      rw [show log c = 420 * log a by linarith [h5] ] at h44 
      have h68 : log a ≠ 0 := by
        exact_mod_cast h4 
      field_simp [h68] at h44 
      all_goals linarith 
    contradiction