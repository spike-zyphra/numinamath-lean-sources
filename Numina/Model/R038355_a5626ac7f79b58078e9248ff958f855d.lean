import Mathlib

theorem algebra_95276 {b c d: ℝ}
    (h : ∀ x y xr yr,
    -- (xr, yr) is the reflection of (x, y) along y = 2x iff
    -- the midpoint lies on the line y = 2x and the slope of
    -- the segment (x, y) - (xr, yr) is -1/2, i.e. perpendicular
    -- to the line y = 2x with slope 2.
    (2 * ((x + xr)/2) = (y + yr)/2 ∧ (yr -y) = -1/2 * (xr-x)) →
    -- We assume that (x, y) lies on C iff (xr, yr) lies on
    -- C*
     (x * y = 1 ↔ 12 * xr ^ 2 + b * xr * yr + c * yr ^ 2 + d = 0)) :
    b * c = 84 := by

  have eq1 := h 1 1 (1/5) (7/5) (by norm_num)
  norm_num at eq1
  have eq2 := h 2 (1/2) (-4/5) (19/10) (by norm_num)
  norm_num at eq2
  have eq3 := h (1/2) 2 (13/10) (8/5) (by norm_num)
  norm_num at eq3
  ring_nf at eq1 eq2 eq3 
  nlinarith