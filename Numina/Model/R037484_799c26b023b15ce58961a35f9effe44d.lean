import Mathlib

theorem algebra_231183 (a b c : ℝ) 
    (h₁ : Real.sin a ≠ 0)
    (h₂ : Real.sin b ≠ 0)
    (h₃ : Real.sin c ≠ 0) : 
    Real.sin (a - b) / (Real.sin a * Real.sin b) + 
    Real.sin (b - c) / (Real.sin b * Real.sin c) + 
    Real.sin (c - a) / (Real.sin c * Real.sin a) = 0 := by
  have h4 : Real.sin (a - b) = Real.sin a * Real.cos b - Real.cos a * Real.sin b := by 
    rw [Real.sin_sub]
  have h5 : Real.sin (b - c) = Real.sin b * Real.cos c - Real.cos b * Real.sin c := by 
    rw [Real.sin_sub]
  have h6 : Real.sin (c - a) = Real.sin c * Real.cos a - Real.cos c * Real.sin a := by
    rw [Real.sin_sub]
  rw [h4, h5, h6]
  have eq1 : (Real.sin a * Real.cos b - Real.cos a * Real.sin b) / (Real.sin a * Real.sin b) = 
    (Real.cos b / Real.sin b) - (Real.cos a / Real.sin a) := by
    field_simp [h₁, h₂]
    <;> ring
  have eq2 : (Real.sin b * Real.cos c - Real.cos b * Real.sin c) / (Real.sin b * Real.sin c) = 
    (Real.cos c / Real.sin c) - (Real.cos b / Real.sin b) := by 
    field_simp [h₂, h₃]
    <;> ring
  have eq3 : (Real.sin c * Real.cos a - Real.cos c * Real.sin a) / (Real.sin c * Real.sin a) = 
    (Real.cos a / Real.sin a) - (Real.cos c / Real.sin c) := by 
    field_simp [h₃, h₁]
    <;> ring
  rw [eq1, eq2, eq3]
  ring