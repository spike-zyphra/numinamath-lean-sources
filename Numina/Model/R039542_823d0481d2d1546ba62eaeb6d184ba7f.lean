import Mathlib

theorem algebra_198564 (x y z : ℝ) :
    x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧
    x^3 = 2 * y^2 - z ∧ y^3 = 2 * z^2 - x ∧ z^3 = 2 * x^2 - y ↔
    (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = 1 ∧ y = 1 ∧ z = 1) := by
  constructor
  · -- Assuming the conditions, proving the result.
    rintro ⟨hx, hy, hz, h1, h2, h3⟩
    have h4 : x^3 + x - 2 * x^2 = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
          mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz 
      ]
    have eq9 : x * (x - 1) ^ 2 = 0 := by
      nlinarith 
    have hx1 : x = 0 ∨ x = 1 := by 
      cases' (mul_eq_zero.1 eq9) with h12 h13
      · -- Case where x =0.
        left
        linarith 
      · -- Case where (x -1)^2 =0
        right
        nlinarith
    -- Similar derivations for y and z
    have h5 : y^3 + y - 2 * y^2 = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
          mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz 
      ]
    have eq8 : y * (y - 1) ^ 2 = 0 := by
      nlinarith 
    have hy1 : y = 0 ∨ y = 1 := by 
      cases' (mul_eq_zero.1 eq8) with h14 h15
      · -- Case where y =0.
        left
        linarith 
      · -- Case where (y -1)^2 =0
        right
        nlinarith
    -- Similarly for z
    have h6 : z^3 + z - 2 * z^2 = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
          mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz 
      ]
    have eq7 : z * (z - 1) ^ 2 = 0 := by
      nlinarith 
    have hz1 : z = 0 ∨ z = 1 := by 
      cases' (mul_eq_zero.1 eq7) with h16 h17
      · -- Case where z =0.
        left
        linarith 
      · -- Case where (z -1)^2 =0
        right
        nlinarith
    rcases hx1 with hx1 | hx1 <;> 
      rcases hy1 with hy1 | hy1 <;> 
        rcases hz1 with hz1 | hz1 <;> 
          ( 
            norm_num [hx1, hy1, hz1] at h1 h2 h3 ⊢ <;> tauto
          )
  · -- Backward implication
    rintro (h | h)
    · -- First solution (0,0,0)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Second solution (1,1,1)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num