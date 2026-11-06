import Mathlib

theorem algebra_247406 :
    {x : ℝ | x ≥ 7 / 4 ∧ ∃ y > 0, y^2 = x + 2 ∧ ∃ z > 0, z^2 = x - 1 ∧ 
    ∃ w > 0, w^2 = 4 * x - 7 ∧ y - z = w} = {2} := by

  ext1 x

  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]

  constructor
  · -- Assume x in left side.
    rintro ⟨hx1, ⟨y, hy, h2, z, hz, h3, w, hw, h4, h5⟩⟩

    have h6 : x = 2 := by
      nlinarith [sq_nonneg (y - z - w), sq_nonneg (y + z - w), sq_nonneg (y * z * w), sq_nonneg ((y - z) ^ 2 - w ^ 2), 
        mul_pos hy hz, mul_pos hy hw, mul_pos hz hw, 
        sq_nonneg (y ^ 2 - (x + 2)), sq_nonneg (z ^ 2 - (x -1)), sq_nonneg (w ^ 2 - (4 * x - 7))]
    linarith
  · -- Assume x in right side.
    intro h
    rw [h]

    constructor
    · norm_num
    · use (2)
      constructor
      · -- Show 2 > 0
        norm_num
      · constructor
        · -- Show (2 : ℝ) ^ 2 = 4
          norm_num
        · use (1)
          constructor
          · -- Show 1 > 0
            norm_num
          · constructor
            · -- Show (1 : ℝ) ^ 2 = 1
              norm_num
            · use (1)
              constructor
              · -- Show 1 > 0
                norm_num
              · -- Show (1 : ℝ) ^ 2 = 1
                norm_num