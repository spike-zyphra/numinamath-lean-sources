import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_195628 :
  IsGreatest {z : ℝ | ∃ x y : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ x + y = 18 ∧ z = sqrt x + sqrt y} 6 := by
  constructor
  · -- Show 6 is in the set
    use 9, 9
    constructor
    · norm_num -- x ≥ 0
    constructor
    · norm_num -- y ≥ 0
    constructor
    · norm_num -- x + y = 18
    · -- Show that sqrt 9 + sqrt 9 = 6
      have h1 : sqrt (9 : ℝ) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1]
      all_goals norm_num
  · -- Show 6 is greatest in the set
    intro z hz
    rcases hz with ⟨x, y, hx, hy, hxy, hz⟩
    have h1 : (sqrt x + sqrt y) ^ 2 ≤ 36 := by
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y,
        sq_nonneg (sqrt x - sqrt y),
        Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith),
        Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith),
        sq_nonneg (x - y),
        hxy]
    have h2 : sqrt x + sqrt y ≤ 6 := by
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, h1, sq_nonneg (sqrt x + sqrt y - 6)]
    nlinarith [hz, h2, Real.sqrt_nonneg x, Real.sqrt_nonneg y]