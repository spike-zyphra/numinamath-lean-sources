import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_298987 :
  IsGreatest {t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ t = (4 * x * z + y * z) / (x ^ 2 + y ^ 2 + z ^ 2)} (Real.sqrt 17 / 2) := by
  constructor
  · -- Show that sqrt 17/2 is indeed in the set
    use 4, 1, Real.sqrt 17
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- Show sqrt 17 > 0
      positivity
    · -- Show that (4 * 4 * sqrt 17 + 1 * sqrt 17) / (4^2 + 1^2 + (sqrt 17)^2) = sqrt 17 / 2
      have h1 : Real.sqrt 17 ^ 2 = 17 := by
        exact Real.sq_sqrt (by norm_num)
      field_simp [h1]
      <;> ring_nf <;> norm_num [Real.sqrt_pos.mpr]
  · -- Show that sqrt 17/2 is the greatest element in the set
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, ht⟩
    have h2 : 0 < x ^ 2 + y ^ 2 + z ^ 2 := by
      nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
    have h3 : (4 * x * z + y * z) ≤ Real.sqrt 17 / 2 * (x^2 + y^2 + z^2) := by
      nlinarith [sq_nonneg (x - 4 * y), sq_nonneg (z - 2 * y * Real.sqrt 17), sq_nonneg (4 * x + y - Real.sqrt 17 * z), sq_nonneg (x ^ 2 + y ^ 2 - z ^ 2), sq_nonneg (4 * x * z + y * z - (Real.sqrt 17 / 2) * (x ^ 2 + y ^ 2 + z ^ 2)), Real.sqrt_nonneg 17, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
    have h4 : (4 * x * z + y * z) / (x ^ 2 + y ^ 2 + z ^ 2) ≤ Real.sqrt 17 / 2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    rw [ht]
    linarith