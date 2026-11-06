import Mathlib

theorem algebra_260551 :
    {(x, y) : ℝ × ℝ | 2 - x + 2 * y ≠ 0 ∧ x + 2 * y - 1 ≠ 0 ∧ 1 - x - 2 * y ≠ 0 ∧ 
                     1 / (2 - x + 2 * y) - 1 / (x + 2 * y - 1) = 2 ∧
                     1 / (2 - x + 2 * y) - 1 / (1 - x - 2 * y) = 4} =
    {(11/6, 1/12)} := by
  ext ⟨x, y⟩
  simp [-one_div]
  constructor
  · -- Assume (x, y) in the set, prove (x, y) = (11/6, 1/12)
    rintro ⟨ha1, ha2, ha3, h1, h2⟩
    have eq1 : 1 / (2 - x + 2 * y) - 1 / (x + 2 * y - 1) = 2 := h1
    have eq2 : 1 / (2 - x + 2 * y) - 1 / (1 - x - 2 * y) = 4 := h2
    field_simp [(show 2 - x + 2 * y ≠ 0 by assumption), 
            (show x + 2 * y - 1 ≠ 0 by assumption)] at eq1
    field_simp [(show 2 - x + 2 * y ≠ 0 by assumption), 
            (show 1 - x - 2 * y ≠ 0 by assumption)] at eq2
    have h4 : x = 11 / 6 := by
      nlinarith [sq_pos_of_ne_zero (show 2 - x + 2 * y ≠ 0 by assumption), 
              sq_pos_of_ne_zero (show x + 2 * y - 1 ≠ 0 by assumption), 
              sq_pos_of_ne_zero (show 1 - x - 2 * y ≠ 0 by assumption)]
    have h5 : y = 1 / 12 := by
      nlinarith [sq_pos_of_ne_zero (show 2 - x + 2 * y ≠ 0 by assumption), 
              sq_pos_of_ne_zero (show x + 2 * y - 1 ≠ 0 by assumption), 
              sq_pos_of_ne_zero (show 1 - x - 2 * y ≠ 0 by assumption)]
    simp [h4, h5]
  · -- Show (11/6, 1/12) in the set
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num