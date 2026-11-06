import Mathlib

theorem algebra_30097 {x y z a : ℝ} (h : Real.cos x + Real.cos y + Real.cos z = a * Real.cos (x + y + z)) (h' : Real.sin x + Real.sin y + Real.sin z = a * Real.sin (x + y + z)) :
    Real.cos (y + z) + Real.cos (z + x) + Real.cos (x + y) = a := by

  have eq1 : Real.cos (y + z) = Real.cos (x + y + z) * Real.cos x + Real.sin (x + y + z) * Real.sin x := by 
    have h1 : Real.cos (y + z) = Real.cos ((x + y + z) - x) := by ring_nf
    rw [h1]
    rw [Real.cos_sub]
    <;> ring_nf <;> simp [Real.sin_add, Real.cos_add] <;> ring_nf

  have eq2 : Real.cos (z + x) = Real.cos (x + y + z) * Real.cos y + Real.sin (x + y + z) * Real.sin y := by 
    have h2 : Real.cos (z + x) = Real.cos ((x + y + z) - y) := by ring_nf
    rw [h2]
    rw [Real.cos_sub]
    <;> ring_nf <;> simp [Real.sin_add, Real.cos_add] <;> ring_nf

  have eq3 : Real.cos (x + y) = Real.cos (x + y + z) * Real.cos z + Real.sin (x + y + z) * Real.sin z := by 
    have h3 : Real.cos (x + y) = Real.cos ((x + y + z) - z) := by ring_nf
    rw [h3]
    rw [Real.cos_sub]
    <;> ring_nf <;> simp [Real.sin_add, Real.cos_add] <;> ring_nf
  
  have eq4 : Real.cos (y + z) + Real.cos (z + x) + Real.cos (x + y) = 
      Real.cos (x + y + z) * (Real.cos x + Real.cos y + Real.cos z) + Real.sin (x + y + z) * (Real.sin x + Real.sin y + Real.sin z) := by
    rw [eq1, eq2, eq3]
    ring

  have eq5 : Real.cos (x + y + z) * (Real.cos x + Real.cos y + Real.cos z) + Real.sin (x + y + z) * (Real.sin x + Real.sin y + Real.sin z) = a := by
    have eq6 : Real.cos x + Real.cos y + Real.cos z = a * Real.cos (x + y + z) := h
    have eq7 : Real.sin x + Real.sin y + Real.sin z = a * Real.sin (x + y + z) := h'
    calc
      Real.cos (x + y + z) * (Real.cos x + Real.cos y + Real.cos z) + Real.sin (x + y + z) * (Real.sin x + Real.sin y + Real.sin z)
          = Real.cos (x + y + z) * (a * Real.cos (x + y + z)) + Real.sin (x + y + z) * (a * Real.sin (x + y + z)) := by
            rw [eq6, eq7]
      _ = a * (Real.cos (x + y + z) ^ 2 + Real.sin (x + y + z) ^ 2) := by 
        ring
      _ = a * (1 : ℝ) := by 
        rw [Real.cos_sq_add_sin_sq (x + y + z)]
        all_goals simp
      _ = a := by 
        ring
  
  rw [eq4, eq5]
  all_goals ring