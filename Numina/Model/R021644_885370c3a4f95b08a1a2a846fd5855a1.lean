import Mathlib

open Real

lemma lemma_1 : 2 * (sqrt 6 + sqrt 5) < 10 := by
  nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 5,
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 6 by norm_num),
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
      sq_nonneg (sqrt 6 - sqrt 5),
      Real.sqrt_le_sqrt (show (5 : ℝ) ≤ 6 by norm_num),
      sq_nonneg (sqrt 6 - 2), sq_nonneg (sqrt 5 - 2),
      Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ),
      sq_nonneg (sqrt 6 ^ 2 - 6), sq_nonneg (sqrt 5 ^ 2 - 5)]


theorem inequalities_320228 :
    Set.ncard {x : ℤ | 1 / (sqrt 3 - sqrt 2) < x ∧ x < 2 / (sqrt 6 - sqrt 5)} = 6 := by

  have h1 : 1 / (sqrt 3 - sqrt 2) = sqrt 3 + sqrt 2 := by
    field_simp [(show sqrt 3 - sqrt 2 ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)]
    )]
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt 3 ^ 2 - 3), sq_nonneg (sqrt 2 ^ 2 - 2)]

  have h2 : 2 / (sqrt 6 - sqrt 5) = 2 * (sqrt 6 + sqrt 5) := by
    field_simp [(show sqrt 6 - sqrt 5 ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 6, Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (5 : ℝ) ≤ (6 : ℝ) by norm_num)]
    )]
    <;> nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (sqrt 6 ^ 2 - 6), sq_nonneg (sqrt 5 ^ 2 - 5)]

  have h3 : {x : ℤ | 1 / (sqrt 3 - sqrt 2) < x ∧ x < 2 / (sqrt 6 - sqrt 5)} = {4, 5, 6, 7, 8, 9} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, h1, h2]
    constructor
    · -- If x ∈ {x : ℤ | sqrt 3 + sqrt 2 < x ∧ x < 2 * (sqrt 6 + sqrt 5)}, then x ∈ {4, 5, 6, 7, 8, 9}
      intro h
      rcases h with ⟨h1, h2⟩
      have h4 : (x : ℝ) > sqrt 3 + sqrt 2 := by
        exact_mod_cast h1
      have h5 : (x : ℝ) < 2 * (sqrt 6 + sqrt 5) := by
        exact_mod_cast h2

      have h6 : sqrt 3 + sqrt 2 < (4 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ), sq_nonneg (sqrt 3 - 1.732), sq_nonneg (sqrt 2 - 1.414), Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ)]

      have h7 : (3 : ℝ) < sqrt 3 + sqrt 2 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ), sq_nonneg (sqrt 3 - 1.732), sq_nonneg (sqrt 2 - 1.414), Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ)]

      have h8 : 2 * (sqrt 6 + sqrt 5) < (10 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ), sq_nonneg (sqrt 6 - sqrt 5), Real.sqrt_le_sqrt (show (5 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (sqrt 6 - 2), sq_nonneg (sqrt 5 - 2), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]

      have h9 : (8 : ℝ) < 2 * (sqrt 6 + sqrt 5) := by
        nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ), sq_nonneg (sqrt 6 - sqrt 5), Real.sqrt_le_sqrt (show (5 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (sqrt 6 - 2), sq_nonneg (sqrt 5 - 2), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]

      have h10 : x > 3 := by
        by_contra h
        push_neg at h
        have h11 : x ≤ 3 := by linarith
        have h12 : (x : ℝ) ≤ (3 : ℝ) := by exact_mod_cast h11
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ), h4, h12]

      have h11 : x < 10 := by
        by_contra h
        push_neg at h
        have h12 : x ≥ 10 := by linarith
        have h13 : (x : ℝ) ≥ (10 : ℝ) := by exact_mod_cast h12
        nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ), h5, h13]

      have h12 : x ≥ 4 := by
        omega
      have h13 : x ≤ 9 := by
        omega

      interval_cases x <;> norm_num at h12 h13 ⊢

    · -- If x ∈ {4, 5, 6, 7, 8, 9}, then x ∈ {x : ℤ | sqrt 3 + sqrt 2 < x ∧ x < 2 * (sqrt 6 + sqrt 5)}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 4
        constructor
        · -- Show sqrt 3 + sqrt 2 < (4 : ℤ)
          have h4 : sqrt 3 + sqrt 2 < (4 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ), sq_nonneg (sqrt 3 - 1.732), sq_nonneg (sqrt 2 - 1.414), Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ)]
          norm_num at *
          exact_mod_cast h4
        · -- Show (4 : ℤ) < 2 * (sqrt 6 + sqrt 5)
          have h5 : (4 : ℝ) < 2 * (sqrt 6 + sqrt 5) := by
            nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ), sq_nonneg (sqrt 6 - sqrt 5), Real.sqrt_le_sqrt (show (5 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (sqrt 6 - 2), sq_nonneg (sqrt 5 - 2), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          norm_num at *
          exact_mod_cast h5
      · -- x = 5
        constructor
        · -- Show sqrt 3 + sqrt 2 < (5 : ℤ)
          have h4 : sqrt 3 + sqrt 2 < (5 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ), sq_nonneg (sqrt 3 - 1.732), sq_nonneg (sqrt 2 - 1.414), Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ)]
          norm_num at *
          exact_mod_cast h4
        · -- Show (5 : ℤ) < 2 * (sqrt 6 + sqrt 5)
          have h5 : (5 : ℝ) < 2 * (sqrt 6 + sqrt 5) := by
            nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ), sq_nonneg (sqrt 6 - sqrt 5), Real.sqrt_le_sqrt (show (5 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (sqrt 6 - 2), sq_nonneg (sqrt 5 - 2), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          norm_num at *
          exact_mod_cast h5
      · -- x = 6
        constructor
        · -- Show sqrt 3 + sqrt 2 < (6 : ℤ)
          have h4 : sqrt 3 + sqrt 2 < (6 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ), sq_nonneg (sqrt 3 - 1.732), sq_nonneg (sqrt 2 - 1.414), Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ)]
          norm_num at *
          exact_mod_cast h4
        · -- Show (6 : ℤ) < 2 * (sqrt 6 + sqrt 5)
          have h5 : (6 : ℝ) < 2 * (sqrt 6 + sqrt 5) := by
            nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ), sq_nonneg (sqrt 6 - sqrt 5), Real.sqrt_le_sqrt (show (5 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (sqrt 6 - 2), sq_nonneg (sqrt 5 - 2), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          norm_num at *
          exact_mod_cast h5
      · -- x = 7
        constructor
        · -- Show sqrt 3 + sqrt 2 < (7 : ℤ)
          have h4 : sqrt 3 + sqrt 2 < (7 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ), sq_nonneg (sqrt 3 - 1.732), sq_nonneg (sqrt 2 - 1.414), Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ)]
          norm_num at *
          exact_mod_cast h4
        · -- Show (7 : ℤ) < 2 * (sqrt 6 + sqrt 5)
          have h5 : (7 : ℝ) < 2 * (sqrt 6 + sqrt 5) := by
            nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ), sq_nonneg (sqrt 6 - sqrt 5), Real.sqrt_le_sqrt (show (5 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (sqrt 6 - 2), sq_nonneg (sqrt 5 - 2), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          norm_num at *
          exact_mod_cast h5
      · -- x = 8
        constructor
        · -- Show sqrt 3 + sqrt 2 < (8 : ℤ)
          have h4 : sqrt 3 + sqrt 2 < (8 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ), sq_nonneg (sqrt 3 - 1.732), sq_nonneg (sqrt 2 - 1.414), Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ)]
          norm_num at *
          exact_mod_cast h4
        · -- Show (8 : ℤ) < 2 * (sqrt 6 + sqrt 5)
          have h5 : (8 : ℝ) < 2 * (sqrt 6 + sqrt 5) := by
            nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ), sq_nonneg (sqrt 6 - sqrt 5), Real.sqrt_le_sqrt (show (5 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (sqrt 6 - 2), sq_nonneg (sqrt 5 - 2), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          norm_num at *
          exact_mod_cast h5
      · -- x = 9
        constructor
        · -- Show sqrt 3 + sqrt 2 < (9 : ℤ)
          have h4 : sqrt 3 + sqrt 2 < (9 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ), sq_nonneg (sqrt 3 - 1.732), sq_nonneg (sqrt 2 - 1.414), Real.mul_self_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ)]
          norm_num at *
          exact_mod_cast h4
        · -- Show (9 : ℤ) < 2 * (sqrt 6 + sqrt 5)
          have h5 : (9 : ℝ) < 2 * (sqrt 6 + sqrt 5) := by
            nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 5, Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ), sq_nonneg (sqrt 6 - sqrt 5), Real.sqrt_le_sqrt (show (5 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (sqrt 6 - 2), sq_nonneg (sqrt 5 - 2), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (5 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          norm_num at *
          exact_mod_cast h5

  rw [h3]
  rw [Set.ncard_eq_toFinset_card']
  simp