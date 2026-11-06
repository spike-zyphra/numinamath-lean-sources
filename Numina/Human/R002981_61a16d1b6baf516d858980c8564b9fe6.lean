import Mathlib

/- 9.3 Two parabolas with different vertices are the graphs of quadratic trinomials with leading coefficients $p$ and $q$. It is known that the vertex of each parabola lies on the other parabola. What can $p+q$ be? -/
theorem algebra_138493 {p q b1 c1 b2 c2 : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (g1 g2 : ℝ → ℝ)
  (h1 : g1 = fun x => p * x ^ 2 + b1 * x + c1)
  (h2 : g2 = fun x => q * x ^ 2 + b2 * x + c2)
  (v1 : g2 (-b1 / (2 * p)) = (4 * p * c1 - b1 ^ 2) / (4 * p))
  (v2 : g1 (-b2 / (2 * q)) = (4 * q * c2 - b2 ^ 2) / (4 * q))
  (v12 : (-b1 / (2 * p)) ≠ (-b2 / (2 * q)))
  : p + q = 0 := by
    -- let (x_1, y_1) be the vertex of the first polynomial
    set x1 := (-b1 / (2 * p))
    set y1 := (4 * p * c1 - b1 ^ 2) / (4 * p)

    -- let (x_2, y_2) be the vertex of the second polynomial
    set x2 := (-b2 / (2 * q))
    set y2 := (4 * q * c2 - b2 ^ 2) / (4 * q)

    -- then we can write the first polynomial as y = p * (x - x_1) ^ 2 + y_1
    replace h1 : g1 = fun x => p * (x - x1) ^ 2 + y1 := by
      ext x
      rw [h1]
      unfold x1 y1

      field_simp
      ring_nf

    -- and the second polynomial as y = q * (x - x_2) ^ 2 + y_2
    replace h2 : g2 = fun x => q * (x - x2) ^ 2 + y2 := by
      ext x
      simp only [h2, x2, y2]

      field_simp
      ring_nf

    -- use that the point (x_2, y_2) lies on the first parabola to get y_2 = p * (x_2 - x_1) ^ 2 + y_1
    have eq_1 : y2 = p * (x2 - x1) ^ 2 + y1 := (h1 ▸ v2).symm

    -- use that the point (x_1, y_1) lies on the second parabola to get y_1 = p * (x_1 - x_2) ^ 2 + y_2
    have eq_2 : y1 = q * (x1 - x2) ^ 2 + y2 := (h2 ▸ v1).symm

    -- add together the equations
    have added : y2 + y1 = (p * (x2 - x1) ^ 2 + y1) + (q * (x1 - x2) ^ 2 + y2) := by linarith

    -- simplify to get (p + q) * (x_1 - x_2) ^ 2 = 0
    have eq_zero : (p + q) * (x1 - x2) ^ 2 = 0 := by linarith

    -- but (x_1 - x_2) ^ 2 is not zero
    have ne_zero : (x1 - x2) ^ 2 ≠ 0 := by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
      rw [sub_eq_zero]
      exact v12

    -- so p + q = 0
    simpa only [mul_eq_zero, ne_zero, or_false] using eq_zero