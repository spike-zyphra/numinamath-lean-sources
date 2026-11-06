import Mathlib

theorem inequalities_598750 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (a ^ 2 * (b + c)) + 1 / (b ^ 2 * (c + a)) + 1 / (c ^ 2 * (a + b)) ≥ 3 / 2 := by
  -- Let x = 1 / a, y = 1 / b, z = 1 / c.
  let x := 1 / a
  let y := 1 / b
  let z := 1 / c
  -- Express the inequality in x, y and z instead.
  have hx : a = 1 / x := by
    field_simp [x]
  have hy : b = 1 / y := by
    field_simp [y]
  have hz : c = 1 / z := by
    field_simp [z]
  have hxyz : x * y * z = 1 := by
    field_simp [x, y, z, habc]
  rw [hx, hy, hz]
  replace ha : 0 < x := by
    field_simp [x, ha]
  replace hb : 0 < y := by
    field_simp [y, hb]
  replace hc : 0 < z := by
    field_simp [z, hc]
  -- Prove the Cauchy-Schwarz inequality.
  have CS_ineq (x₁ y₁ z₁ x₂ y₂ z₂ : ℝ) : (x₁ * x₂ + y₁ * y₂ + z₁ * z₂) ^ 2 ≤ (x₁ ^ 2 + y₁ ^ 2 + z₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2 + z₂ ^ 2) := by
    nlinarith [sq_nonneg (x₁ * y₂ - y₁ * x₂), sq_nonneg (y₁ * z₂ - z₁ * y₂), sq_nonneg (z₁ * x₂ - x₁ * z₂)]
  calc
    _ = x ^ 2 / (1 / (y * z) * (y + z)) + y ^ 2 / (1 / (z * x) * (z + x)) + z ^ 2 / (1 / (x * y) * (x + y)) := by
      field_simp
      ring
    _ = x ^ 2 / (x * (y + z)) + y ^ 2 / (y * (z + x)) + z ^ 2 / (z * (x + y)) := by
      rw [show 1 / (y * z) = x by field_simp; linarith only [hxyz], show 1 / (z * x) = y by field_simp; linarith only [hxyz], show 1 / (x * y) = z by field_simp; linarith only [hxyz]]
    _ ≥ (x + y + z) ^ 2 / (x * (y + z) + y * (z + x) + z * (x + y)) := by
      rw [ge_iff_le, div_le_iff₀ (by positivity)]
      -- Simplify the expression to apply the Cauchy-Schwarz inequality.
      convert CS_ineq (x / Real.sqrt (x * (y + z))) (y / Real.sqrt (y * (z + x))) (z / Real.sqrt (z * (x + y))) (Real.sqrt (x * (y + z))) (Real.sqrt (y * (z + x))) (Real.sqrt (z * (x + y))) using 1
      -- Justify that the inequality to prove agrees with the Cauchy-Schwarz inequality.
      . field_simp
      . clear_value x y z
        iterate 3 rw [div_pow, Real.sq_sqrt (by positivity)]
    _ ≥ 3 / 2 := by
      -- We show that (x + y + z) ^ 2 / (x * (y + z) + y * (z + x) + z * (x + y)) ≥ 3 / 2, which concludes the goal.
      rw [ge_iff_le, div_le_div_iff₀ (by positivity) (by positivity)]
      -- This is equivalent to (x - y)² + (y - z)² + (z - x)² ≥ 0.
      nlinarith only [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]