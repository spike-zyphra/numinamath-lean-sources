import Mathlib.Tactic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.StarOrdered

open NNReal

/-
Let $x, y, z$ be positive real numbers such that $x+y+z=1$. Prove that
$$
\frac{(x+y)^{3}}{z}+\frac{(y+z)^{3}}{x}+\frac{(z+x)^{3}}{y}+9 x y z \geq
  9(x y+y z+z x)
$$
When does equality hold?
-/
theorem inequalities_232997 (x y z : ℝ≥0)  (hsum : x + y + z = 1)
  (pos_x : 0 < x) (pos_y : 0 < y) (pos_z : 0 < z) :
  (x + y)^3 / z + (y + z)^3 / x + (z + x)^3 / y + 9*x*y*z ≥
    9*(x*y + y*z + z*x) ∧ ( x = 1/3 ∧ y = 1/3 ∧ z = 1/3 →
  (x + y)^3 / z + (y + z)^3 / x + (z + x)^3 / y + 9*x*y*z =
    9*(x*y + y*z + z*x)
  ) := by
  -- First show that the equality holds when x = y = z = 1/3
  refine And.intro ?_ $ by
    rintro ⟨hx, hy, hz⟩
    -- Rewrite x, y, and z with 1/3 and clear fractions
    field_simp [hx, hy, hz]
    ring
  -- Prove the inequality
  calc ((x + y)^3 / z + (y + z)^3 / x + (z + x)^3 / y) + 9*x*y*z
    -- Apply the arith-geom mean inequality
    _ ≥ 3 *
      ((x + y)^3 / z).rpow (1/3) *
      ((y + z)^3 / x).rpow (1/3) *
      ((z + x)^3 / y).rpow (1/3) +
        9*x*y*z := by
      -- Specialize to the terms in the lhs
      have := NNReal.geom_mean_le_arith_mean3_weighted
        (1/3) (1/3) (1/3) ((x + y)^3 / z) ((y + z)^3 / x) ((z + x)^3 / y)
        (by field_simp; norm_num)
      -- Move 3 to the other side
      have := mul_le_mul_right' this 3
      -- Distribute the 3
      norm_num [add_mul] at this
      -- Cancel 3 / 3 in each term
      conv_rhs at this => simp [mul_comm, <- mul_assoc]
      -- Apply the modified inequality
      linear_combination this
    -- Simplify cubes and cube roots in the numerators
    _ = 3 * ((x + y) * (y + z) * (z + x)) / (
        x.rpow (1/3) * y.rpow (1/3) * z.rpow (1/3)
    ) + 9*x*y*z := by
      field_simp [div_rpow, <- NNReal.rpow_natCast_mul]
      ring_nf
    -- Apply the arith-geom mean inequality again to the denominator
    _ ≥ 3 * ((x + y) * (y + z) * (z + x)) / (
      (x / 3) + (y / 3) + (z / 3)
    ) + 9*x*y*z := by
      -- Specialize to x, y, z
      have := NNReal.geom_mean_le_arith_mean3_weighted
        (1/3) (1/3) (1/3) x y z
        (by field_simp; norm_num)
      -- Simplify multiplication of fractions
      gcongr
      · field_simp [rpow_pos] -- show the numerator is positive
      -- Apply the arith-geom mean inequality
      simpa only [mul_comm, mul_one_div]
    -- Simplify denominator using hsum, and factor out 9
    _ ≥ 9 * (((x + y) * (y + z) * (z + x)) + x*y*z) := by
      -- Rewrite hsum to fit in the current expression
      have : (x / 3) + (y / 3) + (z / 3) = (1: ℝ≥0) / 3 := by
        field_simp [hsum]
      rw [this, div_div_eq_mul_div, mul_comm]
      norm_num [<- mul_assoc, mul_add]

  -- Divide by 9 on both sides
  refine mul_le_mul_left' ?_ 9
  -- Rearrange terms to factor out x + y + z (so as to apply hsum)
  conv_rhs => calc (x + y) * (y + z) * (z + x) + x * y * z
    _ = (x + y + z) * ((x * y) + (y * z) + (z * x)) := by
      ring
  -- Remove the factor of x + y + z using hsum
  simp [hsum]