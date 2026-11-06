import Mathlib

theorem algebra_275215 :
  {(i1, i2, i3, v) : ℝ × ℝ × ℝ × ℝ | i1 > 0 ∧ i2 > 0 ∧ i3 > 0 ∧ 
    2 = 2 * i1 + i3 ∧ 
    2 = i2 + i3 ∧ 
    i3 = i1 + i2 ∧ 
    v = i3 * 1} =
  {(2/5, 4/5, 6/5, 6/5)} := by
  ext ⟨i1, i2, i3, v⟩
  simp [-one_div]
  constructor
  · -- Assume (i1, i2, i3, v) satisfies the constraints
    rintro ⟨hi1, hi2, hi3, he1, he2, he3, he4⟩
    have eq1 : i1 = 2 / 5 := by
      linarith
    have eq2 : i2 = 4 / 5 := by
      linarith [eq1]
    have eq3 : i3 = 6 / 5 := by 
      linarith [eq1, eq2, he3]
    have eq4 : v = 6 / 5 := by 
      linarith [eq3, he4]
    simp [eq1, eq2, eq3, eq4]
  · -- Show that (2/5, 4/5, 6/5, 6/5) satisfies the constraints
    rintro ⟨rfl, rfl, rfl, rfl⟩
    constructor
    · norm_num -- i1 > 0
    constructor
    · norm_num -- i2 > 0
    constructor
    · norm_num -- i3 > 0
    constructor
    · norm_num -- he1
    constructor
    · norm_num -- he2
    constructor
    · norm_num -- he3
    · norm_num -- he4