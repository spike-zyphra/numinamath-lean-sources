import Mathlib

theorem algebra_226855 {x y z a : ℝ} (ha': Real.cos (x + y + z) ≠ 0) (hb': Real.sin (x + y + z) ≠ 0) (ha : (Real.cos x + Real.cos y + Real.cos z) / Real.cos (x + y + z) = a)
    (hb : (Real.sin x + Real.sin y + Real.sin z) / Real.sin (x + y + z) = a) :
    Real.cos (y + z) + Real.cos (z + x) + Real.cos (x + y) = a := by

  have h1 : Real.cos x + Real.cos y + Real.cos z = a * Real.cos (x + y + z) := by
    have hne : Real.cos (x + y + z) ≠ 0 := ha'
    field_simp [hne] at ha ⊢
    linarith

  have h2 : Real.sin x + Real.sin y + Real.sin z = a * Real.sin (x + y + z) := by
    have hne : Real.sin (x + y + z) ≠ 0 := hb'
    field_simp [hne] at hb ⊢
    linarith

  have h3 : Real.cos (y + z) = Real.cos (x + y + z) * Real.cos x + Real.sin (x + y + z) * Real.sin x := by
    rw [← Real.cos_sub]
    ring

  have h4 : Real.cos (z + x) = Real.cos (x + y + z) * Real.cos y + Real.sin (x + y + z) * Real.sin y := by
    rw [← Real.cos_sub]
    ring

  have h5 : Real.cos (x + y) = Real.cos (x + y + z) * Real.cos z + Real.sin (x + y + z) * Real.sin z := by
    rw [← Real.cos_sub]
    ring

  calc
    Real.cos (y + z) + Real.cos (z + x) + Real.cos (x + y)
        = (Real.cos (x + y + z) * Real.cos x + Real.sin (x + y + z) * Real.sin x) +
          (Real.cos (x + y + z) * Real.cos y + Real.sin (x + y + z) * Real.sin y) + 
          (Real.cos (x + y + z) * Real.cos z + Real.sin (x + y + z) * Real.sin z) := by
      rw [h3, h4, h5]
    _ = Real.cos (x + y + z) * (Real.cos x + Real.cos y + Real.cos z) + Real.sin (x + y + z) * (Real.sin x + Real.sin y + Real.sin z) := by
      ring
    _ = Real.cos (x + y + z) * (a * Real.cos (x + y + z)) + Real.sin (x + y + z) * (a * Real.sin (x + y + z)) := by
      rw [h1, h2]
    _ = a * (Real.cos (x + y + z) ^ 2 + Real.sin (x + y + z) ^ 2) := by
      ring
    _ = a * 1 := by
      have h : Real.cos (x + y + z) ^ 2 + Real.sin (x + y + z) ^ 2 = 1 := by
        exact Real.cos_sq_add_sin_sq (x + y + z)
      rw [h]
    _ = a := by
      ring