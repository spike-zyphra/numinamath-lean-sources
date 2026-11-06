import Mathlib

/-The length of a rectangle is increased by $25\%$, 
  but the width of the rectangle is decreased to keep the area of the rectangle  unchanged.  
  By what percent was the rectangle's width  decreased?-/
theorem algebra_11233 {l w : ℝ} (hl : l > 0) (hw : w > 0)
    (h : l * w = (l * 1.25) * (w * (1 - x))) :
    x = 0.2 := by 
    -- prove the mul_left_cancel of ℝ, so that we have 1 = 1.25 * (1 - x)
    have hx1 : l * w * 1 = l * w * (1.25 * (1 - x)) := by linarith only [h]
    have hx : (l * w)⁻¹ * (l * w * 1) =(l * w)⁻¹ * l * w * (1.25 * (1 - x)) := by rw [hx1]; ring
    field_simp at hx
    -- calculate 1 - x = 0.8
    have eq1 : 1 - x = 0.8 := by
      calc 
        1 - x = 1 / 1.25 := by field_simp; linarith only [hx]
        _ = 0.8 := by norm_num
    -- get the answer x = 0.2 easily
    calc
      x = 1 - (1 - x) := by ring_nf
      _ = 1 - 0.8 := by rw[eq1]
      _ = 0.2 := by norm_num