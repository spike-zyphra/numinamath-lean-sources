import Mathlib

/- The real number $x$ satisfies
\[3x + \frac{1}{2x} = 3.\]Find
\[64x^6 + \frac{1}{729x^6}.\] -/
theorem algebra_21850 {x : ℝ} (hx : x ≠ 0) (h : 3 * x + 1 / (2 * x) = 3) :
    64 * x ^ 6 + 1 / (729 * x ^ 6) = 416 / 27 := by
  -- We have $2x + \frac{1}{3x} = 2$.
  have eq1 : 2 * x + 1 / (3 * x) = 2 := by
    have mid : 2 * x + 1 / (3 * x) = (3 * x + 1 / (2 * x)) * (2 / 3) := by
      ring
    rw [mid, h]
    norm_num
  -- We have $4x^2 + \frac{1}{9x^2} = \frac{8}{3}$.
  have eq2 : 4 * x ^ 2 + 1 / (9 * x ^ 2) = 8 / 3 := by
    have mid : 4 * x ^ 2 + 1 / (9 * x ^ 2) = (2 * x + 1 / (3 * x)) ^ 2 - 4 / 3 := by
      field_simp
      ring
    rw [mid, eq1]
    norm_num
  -- We have $64x^6 + \frac{1}{729x^6} = \left(4x^2 + \frac{1}{9x^2}\right)^3 - \frac{12}{9} \left(4x^2 + \frac{1}{9x^2}\right)$.
  have eq3 : 64 * x ^ 6 + 1 / (729 * x ^ 6) = (4 * x ^ 2 + 1 / (9 * x ^ 2)) ^ 3 - 12 / 9 * (4 * x ^ 2 + 1 / (9 * x ^ 2)) := by
    field_simp
    ring_nf
  -- So $64x^6 + \frac{1}{729x^6} = \frac{8^3}{3^3} - \frac{12}{9} \cdot \frac{8}{3} = \frac{416}{27}$.
  rw [eq3, eq2]
  norm_num