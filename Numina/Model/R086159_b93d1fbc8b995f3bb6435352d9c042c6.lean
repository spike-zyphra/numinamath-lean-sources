import Mathlib

theorem algebra_125065 {x y z a : ℝ} (h₀ : Real.sin (x + y + z) ≠ 0) (h₁ : Real.cos (x + y + z) ≠ 0)
    (h₂ : (Real.sin x + Real.sin y + Real.sin z) / Real.sin (x + y + z) = a)
    (h₃ : (Real.cos x + Real.cos y + Real.cos z) / Real.cos (x + y + z) = a) :
    Real.cos (x + y) + Real.cos (y + z) + Real.cos (z + x) = a := by
  have eq1 : Real.sin x + Real.sin y + Real.sin z = a * Real.sin (x + y + z) := by
    field_simp [h₀] at h₂
    linarith
  have eq2 : Real.cos x + Real.cos y + Real.cos z = a * Real.cos (x + y + z) := by
    field_simp [h₁] at h₃
    linarith
  have h4 : Real.cos (x + y) = Real.cos (x + y + z) * Real.cos z + Real.sin (x + y + z) * Real.sin z := by
    have h : Real.cos (x + y) = Real.cos ((x + y + z) - z) := by ring
    rw [h]
    rw [Real.cos_sub]
    <;> ring_nf <;> field_simp [Real.sin_sq_add_cos_sq] <;> ring
  have h5 : Real.cos (y + z) = Real.cos (x + y + z) * Real.cos x + Real.sin (x + y + z) * Real.sin x := by
    have h : Real.cos (y + z) = Real.cos ((x + y + z) - x) := by ring
    rw [h]
    rw [Real.cos_sub]
    <;> ring_nf <;> field_simp [Real.sin_sq_add_cos_sq] <;> ring
  have h6 : Real.cos (z + x) = Real.cos (x + y + z) * Real.cos y + Real.sin (x + y + z) * Real.sin y := by
    have h : Real.cos (z + x) = Real.cos ((x + y + z) - y) := by ring
    rw [h]
    rw [Real.cos_sub]
    <;> ring_nf <;> field_simp [Real.sin_sq_add_cos_sq] <;> ring
  have h7 : Real.cos (x + y) + Real.cos (y + z) + Real.cos (z + x) = Real.cos (x + y + z) * (Real.cos z + Real.cos x + Real.cos y) + Real.sin (x + y + z) * (Real.sin z + Real.sin x + Real.sin y) := by
    rw [h4, h5, h6]
    ring
  rw [h7]
  have eq3 : Real.cos z + Real.cos x + Real.cos y = a * Real.cos (x + y + z) := by
    linarith [eq2]
  have eq4 : Real.sin z + Real.sin x + Real.sin y = a * Real.sin (x + y + z) := by
    linarith [eq1]
  rw [eq3, eq4]
  have h8 : Real.sin (x + y + z) ^ 2 + Real.cos (x + y + z) ^ 2 = 1 := Real.sin_sq_add_cos_sq (x + y + z)
  have h9 : a * (Real.cos (x + y + z) ^ 2 + Real.sin (x + y + z) ^ 2) = a * 1 := by
    have h10 : Real.cos (x + y + z) ^ 2 + Real.sin (x + y + z) ^ 2 = 1 := by
      linarith [h8]
    rw [show Real.cos (x + y + z) ^ 2 + Real.sin (x + y + z) ^ 2 = 1 by linarith]
    all_goals nlinarith
  calc
    Real.cos (x + y + z) * (a * Real.cos (x + y + z)) + Real.sin (x + y + z) * (a * Real.sin (x + y + z))
        = a * (Real.cos (x + y + z) ^ 2 + Real.sin (x + y + z) ^ 2) := by ring
    _ = a * 1 := by rw [h9]
    _ = a := by ring