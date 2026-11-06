import Mathlib

open Real

/-Let $x,$ $y,$ and $z$ be positive real numbers.  Find the minimum value of
\[\frac{(x^2 + 3x + 1)(y^2 + 3y + 1)(z^2 + 3z + 1)}{xyz}.\]-/
theorem algebra_12097 :
    IsLeast {((x ^ 2 + 3 * x + 1) * (y ^ 2 + 3 * y + 1) * (z ^ 2 + 3 * z + 1)) / (x * y * z) |
      (x : ℝ) (y : ℝ) (z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)} 125 := by
  simp [IsLeast, lowerBounds]
  -- goal devides into two parts
  refine ⟨?_, ?_⟩
  -- prove the inequality can be equal
  . use (1)
    simp
    use (1)
    simp
    use (1)
    norm_num
  -- prove the inequality
  . intro a x y z hx hy hz ha
    have ineq (x : ℝ) : 5 * x ≤ x ^ 2 + 3 * x + 1  := by linarith only [show (x - 1) ^ 2 ≥ 0 by positivity]

    have ineq2 : (5 * x) * (5 * y) * (5 * z) ≤ (x ^ 2 + 3 * x + 1) * (y ^ 2 + 3 * y + 1) * (z ^ 2 + 3 * z + 1) := by
      have ineqx := ineq x
      have ineqy := ineq y
      have ineqz := ineq z

      repeat apply mul_le_mul
      repeat { first | positivity | assumption}
    
    field_simp at ha
    rw [ha] at ineq2
    ring_nf at ineq2
    field_simp at ineq2
    exact ineq2
  