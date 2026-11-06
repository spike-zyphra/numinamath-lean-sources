import Mathlib

theorem algebra_272375 {x y z : ℝ} (h1 : x^2 - y = z^2) (h2 : y^2 - z = x^2) (h3 : z^2 - x = y^2) :
    (x = 1 ∧ y = 0 ∧ z = -1) ∨ (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = 0 ∧ y = -1 ∧ z = 1) ∨ (x = -1 ∧ y = 1 ∧ z = 0) := by
  have h4 : x + y + z = 0 := by
    nlinarith
  
  have h5 : z = -x - y := by linarith

  rw [h5] at h1
  have h6 : y * (y + 2 * x + 1) = 0 := by
    nlinarith
  
  cases' (mul_eq_zero.1 h6) with hy1 hy2
  · -- Case $y = 0$
    have hy0 : y = 0 := by linarith
    have hz0 : z = -x := by 
      linarith [h4, hy0]
    
    have h7 : x * (x - 1) = 0 := by 
      rw [hz0] at h2
      nlinarith

    cases' (mul_eq_zero.1 h7) with hx0 hx1
    · -- x = 0 
      have hx00 : x = 0 := by linarith
      have hz00 : z = 0 := by linarith [hz0, hx00]

      right
      left
      exact ⟨hx00, hy0, hz00⟩
    
    · -- x = 1 
      have hx11 : x = 1 := by linarith
      have hz11 : z = -1 := by linarith [hz0, hx11]

      left 
      exact ⟨hx11, hy0, hz11⟩
  
  · -- Case $y + 2x + 1 = 0$
    have hy22 : y + 2 * x + 1 = 0 := by 
      linarith
    have hy22_eq : y = -2 * x - 1 := by 
      linarith

    have hz2 : z = x + 1 := by 
      linarith [h4, hy22_eq]
    
    have h8 : 3 * x * (x + 1) = 0 := by
      rw [hy22_eq, hz2] at h2
      nlinarith

    cases' (mul_eq_zero.1 h8) with hx0 hx1
    · -- x = 0 
      have hx00 : x = 0 := by linarith
      have hy33 : y = -1 := by 
        linarith [hy22_eq, hx00]
      have hz33 : z = 1 := by 
        linarith [hz2, hx00]

      right 
      right 
      left 
      exact ⟨hx00, hy33, hz33⟩
    
    · -- x + 1 = 0 → x = -1 
      have hx11 : x = -1 := by linarith
      have hy44 : y = 1 := by 
        linarith [hy22_eq, hx11]
      have hz44 : z = 0 := by 
        linarith [hz2, hx11]

      right 
      right 
      right 
      exact ⟨hx11, hy44, hz44⟩
  all_goals linarith