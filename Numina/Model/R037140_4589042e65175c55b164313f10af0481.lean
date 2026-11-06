import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_261361 :
  {p : ℝ | ∃ x y z : ℝ, 25 + 2 * x ^ 2 ≤ 13 * y + 10 * z - p ∧
    25 + 3 * y ^ 2 ≤ 6 * z + 10 * x ∧ 25 + 4 * z ^ 2 ≤ 6 * x + 5 * y + p} = {2} := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume there exists x, y, z such that all three inequalities hold, prove p = 2
    rintro ⟨x, y, z, h1, h2, h3⟩
    have h4 : 2 * (x - 4) ^ 2 + 3 * (y - 3) ^ 2 + 4 * (z - 2) ^ 2 ≤ 0 := by
      nlinarith
    have hx1 : (x - 4) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 3), sq_nonneg (z - 2),
        h4]
    have hy1 : (y - 3) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 3), sq_nonneg (z - 2),
        h4]
    have hz1 : (z - 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 3), sq_nonneg (z - 2),
        h4]
    have hx2 : x = 4 := by
      nlinarith
    have hy2 : y = 3 := by
      nlinarith
    have hz2 : z = 2 := by
      nlinarith
    rw [hx2] at h1 h3
    rw [hy2] at h1 h2 h3
    rw [hz2] at h1 h2 h3
    linarith
  · -- Assume p = 2, prove there exists x, y, z
    intro hp
    rw [hp]
    use 4, 3, 2
    constructor
    · -- Check the first inequality
      norm_num
    constructor
    · -- Check the second inequality
      norm_num
    · -- Check the third inequality
      norm_num