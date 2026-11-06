import Mathlib

/-
23. Let $x, y, z$ be positive real numbers, and $x y z=1$, prove:
$$\frac{x^{3}}{(1+y)(1+z)}+\frac{y^{3}}{(1+z)(1+x)}+\frac{z^{3}}{(1+x)(1+y)} \geqslant \frac{3}{4}$$
(39th IMO Shortlist)
-/
theorem inequalities_602883 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    3 / 4 ≤ x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) +
    z ^ 3 / ((1 + x) * (1 + y)) := by 
  have h1 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) ≥ 3 / 4 := by
    -- First show 3≤x+y+z, by take sqare and use ring lemma.
    have h2 : x + y + z ≥ 3 := by 
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        mul_pos hx hy, mul_pos hy hz, mul_pos hx hz,
        hxyz, sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1)]
    -- Secound step shows that x * y + y * z + z * x ≥ 3 by using similar technique.
    have h3 : x * y + y * z + z * x ≥ 3 := by 
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        mul_pos hx hy, mul_pos hy hz, mul_pos hx hz,
        hxyz, sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1)]
    have h4 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) ≥ 3 / 4 := by
      have h5 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 ≥ 0 := by
        have h6 : (1 + x) * (1 + y) * (1 + z) > 0 := by
          apply mul_pos
          apply mul_pos
          · linarith
          · linarith
          · linarith
        -- Common denominator expansion for each term in the sum.
        have h7 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 = 
          (4 * (x ^ 3 * (1 + x) + y ^ 3 * (1 + y) + z ^ 3 * (1 + z)) - 3 * (1 + x) * (1 + y) * (1 + z)) / (4 * ((1 + x) * (1 + y) * (1 + z))) := by
          field_simp
          ring
        rw [h7]
        -- Simplify numerator and check positivity.
        have h8 : 4 * (x ^ 3 * (1 + x) + y ^ 3 * (1 + y) + z ^ 3 * (1 + z)) - 3 * (1 + x) * (1 + y) * (1 + z) ≥ 0 := by 
          nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
            sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
            sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
            hxyz, h2, h3, mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]
        apply div_nonneg
        · linarith
        · nlinarith [h6]
      linarith
    linarith
  linarith