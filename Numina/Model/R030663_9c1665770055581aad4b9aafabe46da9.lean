import Mathlib

open Real

theorem inequalities_111343 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    3 ≤ x * y + y * z + x * z ↔
    1 / (2 + x) + 1 / (2 + y) + 1 / (2 + z) ≤ 1 := by
  constructor
  · -- Assume 3 ≤ x * y + y * z + x * z, prove 1 / (2 + x) + 1 / (2 + y) + 1 / (2 + z) ≤ 1
    intro h
    have hx1 : 0 < 2 + x := by nlinarith
    have hy1 : 0 < 2 + y := by nlinarith
    have hz1 : 0 < 2 + z := by nlinarith
    have h1 : 1 / (2 + x) + 1 / (2 + y) + 1 / (2 + z) - 1 ≤ 0 := by
      have h2 : (1 / (2 + x) + 1 / (2 + y) + 1 / (2 + z) - 1) =
          ((2 + y) * (2 + z) + (2 + x) * (2 + z) + (2 + x) * (2 + y) - (2 + x) * (2 + y) * (2 + z)) / ((2 + x) * (2 + y) * (2 + z)) := by
        field_simp
        <;> ring
      rw [h2]
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show that the numerator is nonpositive
        nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
                  sq_nonneg (x * y * z - 1), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
                  mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, hxyz, h]
      · -- Show that the denominator is nonnegative
        positivity
    linarith
  · -- Assume 1 / (2 + x) + 1 / (2 + y) + 1 / (2 + z) ≤ 1, prove 3 ≤ x * y + y * z + x * z
    intro h
    have hx1 : 0 < 2 + x := by nlinarith
    have hy1 : 0 < 2 + y := by nlinarith
    have hz1 : 0 < 2 + z := by nlinarith
    have h1 : 1 / (2 + x) + 1 / (2 + y) + 1 / (2 + z) - 1 ≤ 0 := by linarith
    have h2 : (1 / (2 + x) + 1 / (2 + y) + 1 / (2 + z) - 1) =
        ((2 + y) * (2 + z) + (2 + x) * (2 + z) + (2 + x) * (2 + y) - (2 + x) * (2 + y) * (2 + z)) / ((2 + x) * (2 + y) * (2 + z)) := by
      field_simp
      <;> ring
    rw [h2] at h1
    have h3 : (2 + x) * (2 + y) * (2 + z) > 0 := by positivity
    have h4 : (2 + y) * (2 + z) + (2 + x) * (2 + z) + (2 + x) * (2 + y) - (2 + x) * (2 + y) * (2 + z) ≤ 0 := by
      apply (div_nonpos_iff).mp at h1
      cases h1 with
      | inl h1l =>
        nlinarith
      | inr h1r =>
        nlinarith
    nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
              sq_nonneg (x * y * z - 1), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
              mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, hxyz]