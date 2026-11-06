import Mathlib

theorem algebra_16650 {l w : ℝ} (hl : l > 0) (hw : w > 0)
    (hperim : 2 * (l + w) = 56) (hrat : l / w = 4 / 3) :
    Real.sqrt (l^2 + w^2) = 20 := by
  have hsum : l + w = 28 := by
    linarith
  
  have hw_ne_zero : w ≠ 0 := by
    linarith
  
  have h1 : 3 * l = 4 * w := by
    field_simp [hw_ne_zero] at hrat
    linarith
  
  have h2 : l = 4 / 3 * w := by
    linarith
  
  have hw_val : w = 12 := by
    rw [h2] at hsum -- substitute l = 4/3 * w into l + w = 28
    linarith
  
  have hl_val : l = 16 := by
    rw [hw_val] at h2 -- substitute w = 12 into l = 4/3 * w
    linarith
  
  have hdiag : Real.sqrt (l^2 + w^2) = 20 := by
    rw [hl_val, hw_val]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  
  exact hdiag