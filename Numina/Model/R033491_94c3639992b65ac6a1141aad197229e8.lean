import Mathlib

theorem algebra_310543 {x y z a : ℝ} (h1 : Real.cos x + Real.cos y + Real.cos z = a * Real.cos (x + y + z)) (h2 : Real.sin x + Real.sin y + Real.sin z = a * Real.sin (x + y + z)) :
    Real.cos (y + z) + Real.cos (z + x) + Real.cos (x + y) = a := by
  have h7 : Real.cos (y + z) = Real.cos (x + y + z) * Real.cos x + Real.sin (x + y + z) * Real.sin x := by 
    have h8 : y + z = (x + y + z) - x := by ring
    rw [h8]
    rw [Real.cos_sub]
    <;> ring
  have h8 : Real.cos (z + x) = Real.cos (x + y + z) * Real.cos y + Real.sin (x + y + z) * Real.sin y := by 
    have h9 : z + x = (x + y + z) - y := by ring
    rw [h9]
    rw [Real.cos_sub]
    <;> ring
  have h9 : Real.cos (x + y) = Real.cos (x + y + z) * Real.cos z + Real.sin (x + y + z) * Real.sin z := by 
    have h10 : x + y = (x + y + z) - z := by ring
    rw [h10]
    rw [Real.cos_sub]
    <;> ring
  have eq1 : Real.cos (y + z) + Real.cos (z + x) + Real.cos (x + y) = 
      Real.cos (x + y + z) * (Real.cos x + Real.cos y + Real.cos z) + Real.sin (x + y + z) * (Real.sin x + Real.sin y + Real.sin z) := by 
    rw [h7, h8, h9]
    ring
  have h4 : Real.cos (x + y + z) ^ 2 + Real.sin (x + y + z) ^ 2 = 1 := by 
    exact Real.cos_sq_add_sin_sq (x + y + z)
  calc 
    Real.cos (y + z) + Real.cos (z + x) + Real.cos (x + y) = 
      Real.cos (x + y + z) * (Real.cos x + Real.cos y + Real.cos z) + Real.sin (x + y + z) * (Real.sin x + Real.sin y + Real.sin z) := by 
        rw [h7, h8, h9]
        ring
    _ = a * (Real.cos (x + y + z) ^ 2 + Real.sin (x + y + z) ^ 2) := by 
      rw [show Real.cos x + Real.cos y + Real.cos z = a * Real.cos (x + y + z) by linarith [h1] ]
      rw [show Real.sin x + Real.sin y + Real.sin z = a * Real.sin (x + y + z) by linarith [h2] ]
      all_goals ring
    _ = a * (1) := by 
      rw [h4]
    _ = a := by 
      ring