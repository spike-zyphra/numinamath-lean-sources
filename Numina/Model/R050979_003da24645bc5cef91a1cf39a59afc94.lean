import Mathlib

open Real Set

theorem inequalities_278696 :
    IsLeast {t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = 1 ∧ t = 1 / x + 4 / y + 9 / z} 36 := by
  constructor
  · -- Show 36 is in the set
    use 1 / 6, 1 / 3, 1 / 2
    constructor
    · norm_num -- x > 0
    constructor
    · norm_num -- y > 0
    constructor
    · norm_num -- z > 0
    constructor
    · norm_num -- x + y + z = 1
    norm_num -- t = 1 / x + 4 / y + 9 / z
  · -- Show any element in the set is ≥ 36
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, h_eq1, ht_eq⟩
    have h : 1 / x + 4 / y + 9 / z ≥ 36 := by
      have h1 : x * y * z > 0 := by
        apply mul_pos
        apply mul_pos
        all_goals linarith
      have h2 : 1 / x + 4 / y + 9 / z = (y * z + 4 * x * z + 9 * x * y) / (x * y * z) := by
        field_simp
        ring
      have h3 : y * z + 4 * x * z + 9 * x * y ≥ 36 * x * y * z := by
        nlinarith [sq_nonneg (x - 1 / 6), sq_nonneg (y - 1 / 3), sq_nonneg (z - 1 / 2),
                  h_eq1, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
      rw [h2]
      apply (le_div_iff₀' (by positivity)).mpr
      nlinarith
    linarith [ht_eq, h]