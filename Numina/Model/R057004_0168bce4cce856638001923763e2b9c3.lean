import Mathlib
open Real Set

theorem algebra_2933 :
  IsLeast {x : ℝ | ∃ a b : ℝ, a ≥ 3 ∧ b ≥ 3 ∧ x = sqrt (a - 3) + abs (3 - sqrt (b - 3))} 0 := by
  constructor
  · -- We need to show 0 is in the set.
    use 3, 12
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Show the expression equals 0 when a=3 and b=12
      have h1 : sqrt (3 - 3 : ℝ) = 0 := by
        norm_num [sqrt_zero]
      have h2 : sqrt (12 - 3 : ℝ) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h3 : abs (3 - sqrt (12 - 3 : ℝ)) = 0 := by
        rw [h2]
        norm_num
      rw [h1, h3]
      all_goals norm_num 
  · -- Show that any value in the set is ≥ 0
    rintro x ⟨a, b, ha, hb, hx⟩
    have h1 : sqrt (a - 3) ≥ 0 := Real.sqrt_nonneg (a - 3)
    have h2 : abs (3 - sqrt (b - 3)) ≥ 0 := abs_nonneg (3 - sqrt (b - 3))
    have h3 : sqrt (a - 3) + abs (3 - sqrt (b - 3)) ≥ 0 := by linarith
    linarith [hx, h3]