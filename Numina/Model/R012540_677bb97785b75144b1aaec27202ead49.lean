import Mathlib

theorem algebra_142387 (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (x / abs y - abs x / y) * (y / abs z - abs y / z) * (z / abs x - abs z / x) = 0 := by
  by_cases hxy : x ≥ 0
  · -- x ≥ 0
    rw [abs_of_nonneg hxy]
    by_cases hy' : y ≥ 0
    · -- y ≥ 0
      rw [abs_of_nonneg hy']
      by_cases hz' : z ≥ 0
      · -- z ≥ 0
        rw [abs_of_nonneg hz']
        all_goals field_simp [hy, hz, hx] <;> ring_nf <;> norm_num
      · -- z < 0
        rw [abs_of_neg (lt_of_not_ge hz')]
        all_goals field_simp [hy, hz, hx] <;> ring_nf <;> norm_num
    · -- y < 0
      rw [abs_of_neg (lt_of_not_ge hy')]
      by_cases hz' : z ≥ 0
      · -- z ≥ 0
        rw [abs_of_nonneg hz']
        all_goals field_simp [hy, hz, hx] <;> ring_nf <;> norm_num
      · -- z < 0
        rw [abs_of_neg (lt_of_not_ge hz')]
        all_goals field_simp [hy, hz, hx] <;> ring_nf <;> norm_num
  · -- x < 0
    rw [abs_of_neg (lt_of_not_ge hxy)]
    by_cases hy' : y ≥ 0
    · -- y ≥ 0
      rw [abs_of_nonneg hy']
      by_cases hz' : z ≥ 0
      · -- z ≥ 0
        rw [abs_of_nonneg hz']
        all_goals field_simp [hy, hz, hx] <;> ring_nf <;> norm_num
      · -- z < 0
        rw [abs_of_neg (lt_of_not_ge hz')]
        all_goals field_simp [hy, hz, hx] <;> ring_nf <;> norm_num
    · -- y < 0
      rw [abs_of_neg (lt_of_not_ge hy')]
      by_cases hz' : z ≥ 0
      · -- z ≥ 0
        rw [abs_of_nonneg hz']
        all_goals field_simp [hy, hz, hx] <;> ring_nf <;> norm_num
      · -- z < 0
        rw [abs_of_neg (lt_of_not_ge hz')]
        all_goals field_simp [hy, hz, hx] <;> ring_nf <;> norm_num