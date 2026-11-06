import Mathlib

/-
Evaluate the product
\[\left(\sqrt{5}+\sqrt{6}+\sqrt{7}\right)\left(\sqrt{5}+\sqrt{6}-\sqrt{7}\right)\left(\sqrt{5}-\sqrt{6}+\sqrt{7}\right)\left(-\sqrt{5}+\sqrt{6}+\sqrt{7}\right).\]
-/

theorem algebra_94956 : (Real.sqrt 5 + Real.sqrt 6 + Real.sqrt 7) * (Real.sqrt 5 + Real.sqrt 6 - Real.sqrt 7) * (Real.sqrt 5 - Real.sqrt 6 + Real.sqrt 7) * (-Real.sqrt 5 + Real.sqrt 6 + Real.sqrt 7) = 104 := by
  -- Make algebraic substitution for easier calculation
  set x := Real.sqrt 5 with hx
  set y := Real.sqrt 6 with hy
  set z := Real.sqrt 7 with hz
  -- We want to do this because this is a degree four expression, and it is better to square the surds
  calc
    -- Prepare and apply difference of two squares
    (x + y + z) * (x + y - z) * (x - y + z) * (-x + y + z) = (((x + y) + z) * ((x + y) - z)) * ((z + (x - y)) * (z - (x - y))) := by
      ring
    _ = ((x + y)^2 - z^2) * (z^2 - (x - y)^2) := by
      ring
    _ = (x^2 + 2 * x * y + y^2 - z^2) * (z^2 - x^2 + 2 * x * y - y^2) := by
      ring
    -- There are similar terms, so we can do difference of two squares again
    _ = (2 * x * y + (x^2 + y^2 - z^2)) * (2 * x * y - (x^2 + y^2 - z^2)) := by
      ring
    _ = (2 * x * y)^2 - (x^2 + y^2 - z^2)^2 := by
      ring
    -- And at this point, a substitution is easy enough to do by hand
    _ = (2 * (Real.sqrt 5) * (Real.sqrt 6))^2 - ((Real.sqrt 5)^2 + (Real.sqrt 6)^2 - (Real.sqrt 7)^2)^2 := by
      rw [hx, hy, hz]
    _ = 104 := by
      simp [mul_pow]
      norm_num