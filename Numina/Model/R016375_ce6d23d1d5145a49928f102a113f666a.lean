import Mathlib

theorem algebra_196703 (t : ℝ → ℝ) (ht : t = fun x => (1 / 2)^x + (2 / 3)^x + (5 / 6)^x) :
    ∑ᶠ x ∈ {x | (t x - 1) * (t x - 2) * (t x - 3) = 0}, x = 4 := by
  have ht1 : ∀ x, t x = (1 / 2 : ℝ) ^ x + (2 / 3 : ℝ) ^ x + (5 / 6 : ℝ) ^ x := by
    intro x 
    rw [ht]

  have h1 : {x : ℝ | (t x - 1) * (t x - 2) * (t x - 3) = 0} = {0, 1, 3} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Forward implication: if $(t(x) -1)(t(x)-2)(t(x)-3)=0$ then $x \in \{ 0,1,3\}$
      intro h
      have ht2 : (t x - 1) * (t x - 2) * (t x - 3) = 0 := h
      have ht3 : t x - 1 = 0 ∨ t x - 2 = 0 ∨ t x - 3 = 0 := by
        cases (mul_eq_zero.mp ht2) with
        | inl h1 => 
          cases (mul_eq_zero.mp h1) with
          | inl h2 => 
            tauto
          | inr h3 => 
            tauto
        | inr h2 => 
          tauto
      rcases ht3 with ht3 | ht3 | ht3
      · -- Case where t x = 1
        have ht4 : t x = 1 := by linarith
        rw [ht1 x] at ht4
        have h6 : x = 3 := by
          by_cases h7 : x < (3 : ℝ)
          · -- Assume h < 3
            have h8 : (1 / 2 : ℝ) ^ x > (1 / 2 : ℝ) ^ (3 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h9 : (2 / 3 : ℝ) ^ x > (2 / 3 : ℝ) ^ (3 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h10 : (5 / 6 : ℝ) ^ x > (5 / 6 : ℝ) ^ (3 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h11 : (1 / 2 : ℝ) ^ (3 : ℝ) + (2 / 3 : ℝ) ^ (3 : ℝ) + (5 / 6 : ℝ) ^ (3 : ℝ) = (1 : ℝ) := by norm_num
            nlinarith
          by_cases h7 : x > (3 : ℝ)
          · -- Assume h > 3
            have h8 : (1 / 2 : ℝ) ^ x < (1 / 2 : ℝ) ^ (3 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h9 : (2 / 3 : ℝ) ^ x < (2 / 3 : ℝ) ^ (3 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h10 : (5 / 6 : ℝ) ^ x < (5 / 6 : ℝ) ^ (3 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h11 : (1 / 2 : ℝ) ^ (3 : ℝ) + (2 / 3 : ℝ) ^ (3 : ℝ) + (5 / 6 : ℝ) ^ (3 : ℝ) = (1 : ℝ) := by norm_num
            nlinarith
          all_goals linarith
        simp [h6]
        <;> tauto
      · -- Case where t x = 2
        have ht4 : t x = 2 := by linarith
        rw [ht1 x] at ht4
        have h6 : x = 1 := by
          by_cases h7 : x < (1 : ℝ)
          · -- Assume h < 1
            have h8 : (1 / 2 : ℝ) ^ x > (1 / 2 : ℝ) ^ (1 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h9 : (2 / 3 : ℝ) ^ x > (2 / 3 : ℝ) ^ (1 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h10 : (5 / 6 : ℝ) ^ x > (5 / 6 : ℝ) ^ (1 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h11 : (1 / 2 : ℝ) ^ (1 : ℝ) + (2 / 3 : ℝ) ^ (1 : ℝ) + (5 / 6 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by norm_num
            nlinarith
          by_cases h7 : x > (1 : ℝ)
          · -- Assume h > 1
            have h8 : (1 / 2 : ℝ) ^ x < (1 / 2 : ℝ) ^ (1 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h9 : (2 / 3 : ℝ) ^ x < (2 / 3 : ℝ) ^ (1 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h10 : (5 / 6 : ℝ) ^ x < (5 / 6 : ℝ) ^ (1 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h11 : (1 / 2 : ℝ) ^ (1 : ℝ) + (2 / 3 : ℝ) ^ (1 : ℝ) + (5 / 6 : ℝ) ^ (1 : ℝ) = (2 : ℝ) := by norm_num
            nlinarith
          all_goals linarith
        simp [h6]
        <;> tauto
      · -- Case where t x = 3
        have ht4 : t x = 3 := by linarith
        rw [ht1 x] at ht4
        have h6 : x = 0 := by
          by_cases h7 : x < (0 : ℝ)
          · -- Assume h < 0
            have h8 : (1 / 2 : ℝ) ^ x > (1 / 2 : ℝ) ^ (0 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h9 : (2 / 3 : ℝ) ^ x > (2 / 3 : ℝ) ^ (0 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h10 : (5 / 6 : ℝ) ^ x > (5 / 6 : ℝ) ^ (0 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h11 : (1 / 2 : ℝ) ^ (0 : ℝ) + (2 / 3 : ℝ) ^ (0 : ℝ) + (5 / 6 : ℝ) ^ (0 : ℝ) = (3 : ℝ) := by norm_num
            nlinarith
          by_cases h7 : x > (0 : ℝ)
          · -- Assume h > 0
            have h8 : (1 / 2 : ℝ) ^ x < (1 / 2 : ℝ) ^ (0 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h9 : (2 / 3 : ℝ) ^ x < (2 / 3 : ℝ) ^ (0 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h10 : (5 / 6 : ℝ) ^ x < (5 / 6 : ℝ) ^ (0 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_gt
              all_goals linarith
            have h11 : (1 / 2 : ℝ) ^ (0 : ℝ) + (2 / 3 : ℝ) ^ (0 : ℝ) + (5 / 6 : ℝ) ^ (0 : ℝ) = (3 : ℝ) := by norm_num
            nlinarith
          all_goals linarith
        simp [h6]
        <;> tauto
    · -- Backward implication: if $x \in \{ 0,1,3\}$ then $(t(x)-1)(t(x)-2)(t(x)-3)=0$
      rintro (rfl | rfl | rfl)
      · -- Case where x = 0
        norm_num [ht1]
      · -- Case where x = 1
        norm_num [ht1]
      · -- Case where x = 3
        norm_num [ht1]
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> norm_num
  all_goals linarith