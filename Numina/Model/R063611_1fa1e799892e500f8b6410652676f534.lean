import Mathlib

theorem algebra_19863 : Real.sqrt 72 / Real.sqrt 10 = (6 * Real.sqrt 5) / 5 := by
  have h1 : Real.sqrt 72 / Real.sqrt 10 = Real.sqrt (72 / 10) := by
    field_simp [Real.sqrt_div]
    all_goals norm_num

  rw [h1]

  have h2 : Real.sqrt (72 / 10) = Real.sqrt (36 / 5) := by
    norm_num

  rw [h2]

  have h3 : Real.sqrt (36 / 5) = Real.sqrt 36 / Real.sqrt 5 := by
    field_simp [Real.sqrt_div]
    all_goals norm_num

  rw [h3]

  have h4 : Real.sqrt 36 = 6 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

  rw [h4]

  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show 5 ≥ 0 by norm_num)

  field_simp [h5]
  <;> ring_nf <;> norm_num
  all_goals ring_nf <;> norm_num