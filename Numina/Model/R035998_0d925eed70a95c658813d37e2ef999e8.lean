import Mathlib

theorem algebra_288203 :
  {(a, b, c) : ℤ × ℤ × ℤ | a + b + c = 35 ∧ a + c = 2 * b - 1 ∧ b^2 = (a + 3) * c} =
  {(15, 12, 8), (5, 12, 18)} := by
  ext ⟨a, b, c⟩
  simp
  constructor
  · -- Assume (a, b, c) satisfies all three conditions
    rintro ⟨h1, h2, h3⟩
    
    have eq1 : b = 12 := by
      have eq2 : a + c = 2 * b - 1 := by linarith
      have eq3 : a + b + c = 35 := by linarith
      nlinarith
    
    have eq2 : a + c = 23 := by
      rw [eq1] at h2
      linarith
    
    have eq3 : 144 = (a + 3) * c := by 
      rw [eq1] at h3
      linarith
    
    have eq4 : a = 23 - c := by 
      omega
    
    rw [eq4] at eq3
    have h4 : c ^ 2 - 26 * c + 144 = 0 := by 
      linarith
    
    have h5 : c = 8 ∨ c = 18 := by 
      have h4' : c ^ 2 - 26 * c + 144 = 0 := h4
      have h6 : c ≤ 26 := by nlinarith
      have h7 : c ≥ 0 := by nlinarith
      interval_cases c <;> omega

    rcases h5 with (h5 | h5)
    · -- c = 8
      have hc8 : c = 8 := h5
      have ha15 : a = 15 := by 
        linarith
      simp [ha15, eq1, hc8]
    
    · -- c = 18
      have hc18 : c = 18 := h5
      have ha5 : a = 5 := by 
        linarith
      simp [ha5, eq1, hc18]
  
  · -- Show that both pairs satisfy the conditions.
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · -- Check (15, 12, 8)
      constructor
      · -- Check a + b + c = 35
        norm_num
      constructor
      · -- Check a + c = 2 * b - 1
        norm_num
      · -- Check b^2 = (a + 3) * c
        norm_num
    · -- Check (5, 12, 18)
      constructor
      · -- Check a + b + c = 35
        norm_num
      constructor
      · -- Check a + c = 2 * b - 1
        norm_num
      · -- Check b^2 = (a + 3) * c
        norm_num