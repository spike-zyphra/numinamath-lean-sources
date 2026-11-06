import Mathlib

theorem algebra_296937 (a b : ℝ) (ha : a ≠ 0) (h0 : 0 < 3 * a * 0 ^ 2 + 2 * b * 0 - (a + b)) (h1 : 0 < 3 * a * 1 ^ 2 + 2 * b * 1 - (a + b)) :
    {x | 0 < x ∧ x < 1 ∧ 3 * a * x ^ 2 + 2 * b * x - (a + b) = 0}.encard = 2 := by
  have h2 : a + b < 0 := by
    linarith
  have h3 : 2 * a + b > 0 := by
    linarith
  have h4 : a > 0 := by
    nlinarith
  have h5 : 3 * a > 0 := by
    nlinarith
  have h6 : 0 < b ^ 2 + 3 * a * (a + b) := by
    nlinarith [h2, h3, sq_pos_of_pos h4, sq_nonneg (b + a), sq_nonneg (b + 2 * a)]
  have h7 : {x | 0 < x ∧ x < 1 ∧ 3 * a * x ^ 2 + 2 * b * x - (a + b) = 0} = { 
    (-b + Real.sqrt (b ^ 2 + 3 * a * (a + b))) / (3 * a), 
    (-b - Real.sqrt (b ^ 2 + 3 * a * (a + b))) / (3 * a)
  } := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x in the roots set
      rintro ⟨hx0, hx1, heq⟩
      have h8 : 3 * a * x ^ 2 + 2 * b * x - (a + b) = 0 := heq
      have h9 : (x - (-b + Real.sqrt (b ^ 2 + 3 * a * (a + b))) / (3 * a)) * 
        (x - (-b - Real.sqrt (b ^ 2 + 3 * a * (a + b))) / (3 * a)) = 0 := by
        have h8' : 3 * a * x ^ 2 + 2 * b * x - (a + b) = 0 := heq
        field_simp [(show 3 * a ≠ 0 by 
            intro h
            apply ha
            linarith
        )] at *
        nlinarith [Real.sqrt_pos.mpr (show b ^ 2 + 3 * a * (a + b) > 0 by linarith), 
          Real.sq_sqrt (show b ^ 2 + 3 * a * (a + b) ≥ 0 by linarith), 
          sq_nonneg (x * (3 * a) + b), sq_nonneg (x * (3 * a) + b + Real.sqrt (b ^ 2 + 3 * a * (a + b)))
        ]
      cases' (mul_eq_zero.mp h9) with h10 h11
      · -- First root
        left
        linarith
      · -- Second root
        right
        linarith
    · -- Show the defined roots are in the set.
      rintro (rfl | rfl)
      · -- First root
        constructor
        · -- Show 0 < x
          have hx01 : 0 < (-b + Real.sqrt (b ^ 2 + 3 * a * (a + b))) / (3 * a) := by
            apply div_pos
            -- Show numerator is positive
            have h11 : -b + Real.sqrt (b ^ 2 + 3 * a * (a + b)) > 0 := by
              nlinarith [Real.sqrt_pos.mpr (show b ^ 2 + 3 * a * (a + b) > 0 by linarith), 
                Real.sq_sqrt (show b ^ 2 + 3 * a * (a + b) ≥ 0 by linarith)
              ]
            linarith
            all_goals linarith [h5]
          linarith
        constructor
        · -- Show x < 1
          have hx011 : (-b + Real.sqrt (b ^ 2 + 3 * a * (a + b))) / (3 * a) < 1 := by
            apply (div_lt_iff₀ (by linarith)).mpr
            nlinarith [Real.sqrt_pos.mpr (show b ^ 2 + 3 * a * (a + b) > 0 by linarith), 
              Real.sq_sqrt (show b ^ 2 + 3 * a * (a + b) ≥ 0 by linarith), 
                sq_nonneg (b + a), sq_nonneg (b - a)
            ]
          linarith
        · -- Show equation = 0
          field_simp [(show 3 * a ≠ 0 by 
            intro h
            apply ha
            linarith
          )]
          nlinarith [Real.sqrt_pos.mpr (show b ^ 2 + 3 * a * (a + b) > 0 by linarith), 
            Real.sq_sqrt (show b ^ 2 + 3 * a * (a + b) ≥ 0 by linarith), 
              sq_nonneg ((-b + Real.sqrt (b ^ 2 + 3 * a * (a + b))) * (3 * a) + b)
            ]
      · -- Second root
        constructor
        · -- Show 0 < x
          have hx00 : 0 < (-b - Real.sqrt (b ^ 2 + 3 * a * (a + b))) / (3 * a) := by
            apply div_pos
            -- Show numerator is positive
            have h12 : -b - Real.sqrt (b ^ 2 + 3 * a * (a + b)) > 0 := by
              nlinarith [Real.sqrt_pos.mpr (show b ^ 2 + 3 * a * (a + b) > 0 by linarith), 
                Real.sq_sqrt (show b ^ 2 + 3 * a * (a + b) ≥ 0 by linarith)
              ]
            linarith
            all_goals linarith [h5]
          linarith
        constructor
        · -- Show x < 1
          have hx011 : (-b - Real.sqrt (b ^ 2 + 3 * a * (a + b))) / (3 * a) < 1 := by
            apply (div_lt_iff₀ (by linarith)).mpr
            nlinarith [Real.sqrt_pos.mpr (show b ^ 2 + 3 * a * (a + b) > 0 by linarith), 
              Real.sq_sqrt (show b ^ 2 + 3 * a * (a + b) ≥ 0 by linarith), 
                sq_nonneg (b + a), sq_nonneg (b - a)
            ]
          linarith
        · -- Show equation = 0
          field_simp [(show 3 * a ≠ 0 by 
            intro h
            apply ha
            linarith
          )]
          nlinarith [Real.sqrt_pos.mpr (show b ^ 2 + 3 * a * (a + b) > 0 by linarith), 
            Real.sq_sqrt (show b ^ 2 + 3 * a * (a + b) ≥ 0 by linarith), 
              sq_nonneg ((-b - Real.sqrt (b ^ 2 + 3 * a * (a + b))) * (3 * a) + b)
            ]
  rw [h7]
  have h8 : (-b + Real.sqrt (b ^ 2 + 3 * a * (a + b))) / (3 * a) ≠ (-b - Real.sqrt (b ^ 2 + 3 * a * (a + b))) / (3 * a) := by
    by_contra h
    have h9 : Real.sqrt (b ^ 2 + 3 * a * (a + b)) = 0 := by
      have h5' : 3 * a ≠ 0 := by
        intro h
        apply ha
        linarith
      field_simp [h5'] at h ⊢
      <;> nlinarith [Real.sqrt_nonneg (b ^ 2 + 3 * a * (a + b)), Real.sq_sqrt (show b ^ 2 + 3 * a * (a + b) ≥ 0 by linarith)]
    have h10 : b ^ 2 + 3 * a * (a + b) = 0 := by
      rw [Real.sqrt_eq_zero (by nlinarith) ] at h9
      linarith
    nlinarith [h6, h10]
  rw [Set.encard_pair h8]
  all_goals norm_num