import Mathlib

/-If $x+\frac{1}{y}=1$ and $y+\frac{1}{z}=1$, what is the value of the product $xyz$?-/
theorem algebra_15765 {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (h₀ : x + 1 / y = 1) (h₁ : y + 1 / z = 1) :
    x * y * z = -1 := by 
  -- prove the equation x * y + 1 = y
  have eq₁ : x * y + 1 = y := by
    calc
      x * y + 1 = (x * y + 1) / y * y := by rw [div_mul_cancel₀]; exact hy
      _ = (x + 1 / y) * y := by rw [add_div']; exact hy
      _ = y := by rw [h₀]; ring_nf
  -- similarly prove the equation y * z + 1 = z
  have eq₂ : y * z + 1 = z := by
    calc
      y * z + 1 = (y * z + 1) / z * z := by rw [div_mul_cancel₀]; exact hz
      _ = (y + 1 / z) * z := by rw [add_div']; exact hz
      _ = z := by rw [h₁]; ring_nf
  -- substitute the y in eq₂ by eq₁ 
  rw [<-eq₁] at eq₂
  -- simplify to x * y * z + z + 1 = z
  replace eq₂ : x * y * z + z + 1 = z := by ring_nf at eq₂ ⊢; exact eq₂
  -- finally get the conclusion
  calc 
    x * y * z = (x * y * z + z + 1) - z - 1 := by ring_nf
    _ = z - z - 1 := by rw [eq₂]
    _ = -1 := by ring_nf 
  