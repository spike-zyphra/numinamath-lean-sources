import Mathlib

theorem algebra_149 : {x : ℤ | (x ^ 2 + x - 1 : ℝ) ^ (x + 2) = 1}.encard = 3 := by
  have h1 : {x : ℤ | (x ^ 2 + x - 1 : ℝ) ^ (x + 2) = 1} = {-2, 0, 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume h : (x ^ 2 + x - 1 : ℝ) ^ (x + 2) = 1, prove x ∈ {-2, 0, 1}
      intro h
      have eq1 : (x ^ 2 + x - 1 : ℝ) ^ (x + 2 : ℝ) = 1 := by
        exact_mod_cast h
      have h2 : x ≤ 1 := by
        by_contra h
        push_neg at h
        have h3 : x ≥ 2 := by omega
        have h4 : x ≥ 2 := by linarith
        have h5 : (x : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h4
        have eq4 : (x ^ 2 + x - 1 : ℝ) ≥ (3 : ℝ) := by
          nlinarith [sq_nonneg ((x : ℝ) : ℝ)]
        have h7 : (x + 2 : ℝ) ≥ (4 : ℝ) := by
          have h5' : (x : ℝ) ≥ (2 : ℝ) := h5
          linarith
        have h22 : (x ^ 2 + x - 1 : ℝ) ^ (x + 2 : ℝ) ≥ (3 : ℝ) ^ (4 : ℝ) := by
          have h23 : (3 : ℝ) ^ (4 : ℝ) ≤ (x ^ 2 + x - 1 : ℝ) ^ (4 : ℝ) := by
            apply Real.rpow_le_rpow
            · -- Show 0 ≤ (3 : ℝ)
              norm_num
            · -- Show (3 : ℝ) ≤ (x ^ 2 + x - 1 : ℝ)
              nlinarith
            · -- Show (4 : ℝ) ≥ 0
              norm_num
          have h24 : (x ^ 2 + x - 1 : ℝ) ^ (4 : ℝ) ≤ (x ^ 2 + x - 1 : ℝ) ^ (x + 2 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le
            · -- Show 1 ≤ (x ^ 2 + x - 1 : ℝ)
              nlinarith
            · -- Show (4 : ℝ) ≤ (x + 2 : ℝ)
              linarith
          have h25 : (3 : ℝ) ^ (4 : ℝ) ≤ (x ^ 2 + x - 1 : ℝ) ^ (x + 2 : ℝ) := by
            nlinarith [h23, h24]
          linarith
        have h29 : (3 : ℝ) ^ (4 : ℝ) = (81 : ℝ) := by norm_num
        nlinarith [h29, eq1, h22]
      have h3 : x ≥ -2 := by
        by_contra h
        push_neg at h
        have h4 : x ≤ -3 := by omega
        have h5 : (x : ℝ) ≤ (-3 : ℝ) := by exact_mod_cast h4
        have h10 : (x ^ 2 + x - 1 : ℝ) > 0 := by
          nlinarith [sq_nonneg ((x : ℝ) : ℝ)]
        have eq2 : (x ^ 2 + x - 1 : ℝ) ^ (x + 2 : ℝ) = 1 := eq1
        have h11 : (x + 2 : ℝ) * Real.log ((x ^ 2 + x - 1 : ℝ)) = 0 := by
          have h12 : Real.log ((x ^ 2 + x - 1 : ℝ) ^ (x + 2 : ℝ)) = Real.log (1 : ℝ) := by
            rw [eq2]
          have h13 : Real.log ((x ^ 2 + x - 1 : ℝ) ^ (x + 2 : ℝ)) = (x + 2 : ℝ) * Real.log ((x ^ 2 + x - 1 : ℝ)) := by
            rw [Real.log_rpow]
            all_goals
              try positivity
          have h14 : Real.log (1 : ℝ) = 0 := Real.log_one
          linarith [h12, h13, h14]
        cases (mul_eq_zero.mp h11) with
        | inl h15 =>
          have h16 : x = -2 := by
            have h17 : (x : ℝ) = (-2 : ℝ) := by
              linarith
            exact_mod_cast h17
          omega
        | inr h17 =>
          have h18 : Real.log ((x ^ 2 + x - 1 : ℝ)) = 0 := by
            linarith
          have h19 : (x ^ 2 + x - 1 : ℝ) = 1 := by
            rw [Real.log_eq_zero] at h18
            rcases h18 with (r | r | r)
            · linarith
            · linarith
            · linarith
          have h20 : x = -2 ∨ x = 1 := by
            have h21 : x ^ 2 + x - 2 = 0 := by
              have h22 : (x : ℝ) ^ 2 + (x : ℝ) - 2 = 0 := by
                nlinarith
              exact_mod_cast h22
            have h23 : (x + 2) * (x - 1) = 0 := by
              nlinarith
            cases (mul_eq_zero.mp h23) with
            | inl h24 =>
              left
              linarith
            | inr h25 =>
              right
              linarith
          cases h20 with
          | inl h22 =>
            omega
          | inr h24 =>
            omega
      interval_cases x <;> norm_num at eq1 ⊢ 
    · -- Assume x ∈ {-2, 0, 1}, prove (x ^ 2 + x - 1 : ℝ) ^ (x + 2) = 1
      rintro (rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  rw [Set.encard]
  simp