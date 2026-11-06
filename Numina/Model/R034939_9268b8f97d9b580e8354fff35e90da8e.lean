import Mathlib

open Real

theorem algebra_286720 :
    IsLeast {t : ℝ | ∃ x y z : ℝ, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ t = ((x * y / z + z * x / y + y * z / x) *
      (x / (y * z) + y / (z * x) + z / (x * y)))} 9 := by
  constructor
  · -- Show 9 is achievable with x=y=z=1
    use 1, 1, 1
    norm_num
  · -- Show that no value less than 9 is in the set
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, ht⟩
    have h1 : ((x * y / z + z * x / y + y * z / x) * (x / (y * z) + y / (z * x) + z / (x * y))) ≥ 9 := by
      have h2 : (x * y / z + z * x / y + y * z / x) * (x / (y * z) + y / (z * x) + z / (x * y)) =
        (x^2 * y^2 + y^2 * z^2 + x^2 * z^2) * (x^2 + y^2 + z^2) / (x^2 * y^2 * z^2) := by
        field_simp
        <;> ring_nf <;> field_simp
        <;> ring
      rw [h2] at *
      have hx1 : x^2 > 0 := by
        exact sq_pos_of_ne_zero hx
      have hy1 : y^2 > 0 := by
        exact sq_pos_of_ne_zero hy
      have hz1 : z^2 > 0 := by
        exact sq_pos_of_ne_zero hz
      have hx2 : x^2 * y^2 * z^2 > 0 := by
        positivity
      have hx3 : (x^2 * y^2 + y^2 * z^2 + x^2 * z^2) * (x^2 + y^2 + z^2) ≥ 9 * (x^2 * y^2 * z^2) := by
        nlinarith [sq_nonneg (x^2 * y^2 - y^2 * z^2), sq_nonneg (x^2 * y^2 - x^2 * z^2), sq_nonneg (y^2 * z^2 - x^2 * z^2), 
            sq_nonneg (x^2 - y^2), sq_nonneg (x^2 - z^2), sq_nonneg (y^2 - z^2), 
            mul_pos hx1 hy1, mul_pos hx1 hz1, mul_pos hy1 hz1, 
            sq_nonneg (x * y - y * z), sq_nonneg (x * y - z * x), sq_nonneg (y * z - x * z)
          ]
      have hx4 : (x^2 * y^2 + y^2 * z^2 + x^2 * z^2) * (x^2 + y^2 + z^2) / (x^2 * y^2 * z^2) ≥ 9 := by
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith
      linarith
    linarith [ht, h1]