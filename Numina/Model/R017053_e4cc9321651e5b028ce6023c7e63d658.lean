import Mathlib

open Real


theorem algebra_96733 (a : ℝ) :
    {x : ℝ | ∃ y : ℝ, x^2 + y^2 = a^2 ∧ y = x^2 - a}.encard = 3 ↔ a > 1 / 2 := by
  constructor
  · -- Assume {x : ℝ | ∃ y : ℝ, x^2 + y^2 = a^2 ∧ y = x^2 - a}.encard = 3, prove a > 1 / 2
    intro h
    by_contra h1
    push_neg at h1
    have h2 : {x : ℝ | ∃ y : ℝ, x^2 + y^2 = a^2 ∧ y = x^2 - a} = {0} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · -- Assume x in {x : ℝ | ... }
        rintro ⟨y, h_eq1, h_eq2⟩
        -- Substitute y = x^2 - a into x^2 + y^2 = a^2
        have h_eq3 : x^2 + (x^2 - a)^2 = a^2 := by
          have h_eq3 : y = x^2 - a := by linarith
          rw [show y = x^2 - a by linarith] at h_eq1
          nlinarith
        have h_eq4 : x^2 * (x^2 + (1 - 2 * a)) = 0 := by
          nlinarith
        cases' (mul_eq_zero.1 h_eq4) with h_eq5 h_eq6
        · -- Case $h_eq5$, i.e. $x^2 = 0$
          have : x = 0 := by
            nlinarith
          tauto
        · -- Case $h_eq6$, i.e. x^2 + (1 - 2a) = 0
          have h_eq7 : x^2 = (2 * a - 1 : ℝ) := by
            nlinarith
          have h_eq8 : (2 * a - 1 : ℝ) ≤ 0 := by nlinarith
          have h_eq9 : x^2 = 0 := by
            nlinarith [sq_nonneg x]
          have : x = 0 := by
            nlinarith
          tauto
      · -- Assume x = 0
        intro h_eq3
        rw [h_eq3]
        use -a
        constructor
        · -- Show x^2 + y^2 = a^2
          nlinarith
        · -- Show y = x^2 - a
          nlinarith
    rw [h2] at h
    simp at h
  · -- Assume a > 1 / 2, prove {x : ℝ | ∃ y : ℝ, x^2 + y^2 = a^2 ∧ y = x^2 - a}.encard = 3
    intro ha
    have h3 : {x : ℝ | ∃ y : ℝ, x^2 + y^2 = a^2 ∧ y = x^2 - a} = {0, Real.sqrt (2 * a - 1), -Real.sqrt (2 * a - 1)} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
      constructor
      · -- First direction: from x in {x | ...} to membership in {0, sqrt ..., -sqrt ...}
        rintro ⟨y, h_eq1, h_eq2⟩
        have h_eq3 : x^2 * (x^2 + (1 - 2 * a)) = 0 := by
          have h_eq3 : y = x^2 - a := by linarith
          rw [show y = x^2 - a by linarith] at h_eq1
          nlinarith
        cases' (mul_eq_zero.1 h_eq3) with h_eq4 h_eq5
        · -- First case, h_eq4: x^2 = 0
          have h_eq6 : x = 0 := by
            nlinarith
          rw [h_eq6]
          norm_num
        · -- Second case, h_eq5: x^2 + (1 - 2 * a) = 0
          have h_eq6 : x^2 = (2 * a - 1 : ℝ) := by
            nlinarith
          have h_eq7 : 2 * a - 1 > 0 := by
            linarith
          have h_eq10 : (x - Real.sqrt (2 * a - 1)) * (x + Real.sqrt (2 * a - 1)) = 0 := by
            have h_eq8 : x^2 = (2 * a - 1 : ℝ) := h_eq6
            have h_eq9 : x^2 - (2 * a - 1 : ℝ) = 0 := by
              linarith
            have h_eq10 : x^2 - (2 * a - 1 : ℝ) = (x - Real.sqrt (2 * a - 1)) * (x + Real.sqrt (2 * a - 1)) := by
              nlinarith [Real.sqrt_nonneg (2 * a - 1 : ℝ), Real.sq_sqrt (show 0 ≤ (2 * a - 1 : ℝ) by linarith)]
            nlinarith
          cases' (mul_eq_zero.1 h_eq10) with h_eq11 h_eq12
          · -- First case, h_eq11: x - Real.sqrt (2 * a - 1) = 0
            have h_eq13 : x = Real.sqrt (2 * a - 1) := by linarith
            simp [h_eq13]
          · -- Second case, h_eq12: x + Real.sqrt (2 * a - 1) = 0
            have h_eq13 : x = -Real.sqrt (2 * a - 1) := by linarith
            simp [h_eq13]
      · -- Second direction: from membership in {0, sqrt ..., -sqrt ...} to x in {x | ...}
        rintro (rfl | rfl | rfl)
        · -- First case: x = 0
          use -a
          constructor
          · -- Check x^2 + y^2 = a^2
            nlinarith
          · -- Check y = x^2 - a
            nlinarith
        · -- Second case: x = Real.sqrt (2 * a - 1)
          use (a - 1 : ℝ)
          constructor
          · -- Check x^2 + y^2 = a^2
            have h_eq7 : 2 * a - 1 > 0 := by
              linarith
            have h_eq8 : (Real.sqrt (2 * a - 1) : ℝ)^2 = (2 * a - 1 : ℝ) := by
              rw [Real.sq_sqrt]
              linarith
            nlinarith [Real.sqrt_nonneg (2 * a - 1)]
          · -- Check y = x^2 - a
            have h_eq7 : 2 * a - 1 > 0 := by
              linarith
            have h_eq8 : (Real.sqrt (2 * a - 1) : ℝ)^2 = (2 * a - 1 : ℝ) := by
              rw [Real.sq_sqrt]
              linarith
            nlinarith [Real.sqrt_nonneg (2 * a - 1)]
        · -- Third case: x = -Real.sqrt (2 * a - 1)
          use (a - 1 : ℝ)
          constructor
          · -- Check x^2 + y^2 = a^2
            have h_eq7 : 2 * a - 1 > 0 := by
              linarith
            have h_eq8 : (-Real.sqrt (2 * a - 1) : ℝ)^2 = (2 * a - 1 : ℝ) := by
              have h_eq9 : (Real.sqrt (2 * a - 1) : ℝ)^2 = (2 * a - 1 : ℝ) := by
                rw [Real.sq_sqrt]
                linarith
              nlinarith [Real.sqrt_nonneg (2 * a - 1)]
            nlinarith [Real.sqrt_nonneg (2 * a - 1)]
          · -- Check y = x^2 - a
            have h_eq7 : 2 * a - 1 > 0 := by
              linarith
            have h_eq8 : (-Real.sqrt (2 * a - 1) : ℝ)^2 = (2 * a - 1 : ℝ) := by
              have h_eq9 : (Real.sqrt (2 * a - 1) : ℝ)^2 = (2 * a - 1 : ℝ) := by
                rw [Real.sq_sqrt]
                linarith
              nlinarith [Real.sqrt_nonneg (2 * a - 1)]
            nlinarith [Real.sqrt_nonneg (2 * a - 1)]
    rw [h3]
    have h_eq7 : 2 * a - 1 > 0 := by
      linarith
    have h_eq8 : Real.sqrt (2 * a - 1) > 0 := by
      positivity
    have h9 : ({0, Real.sqrt (2 * a - 1), -Real.sqrt (2 * a - 1)} : Set ℝ).encard = 3 := by
      have h_ne1 : (0 : ℝ) ≠ Real.sqrt (2 * a - 1) := by
        nlinarith [Real.sqrt_nonneg (2 * a - 1 : ℝ), Real.sq_sqrt (show 0 ≤ (2 * a - 1 : ℝ) by linarith)]
      have h_ne2 : (0 : ℝ) ≠ -Real.sqrt (2 * a - 1) := by
        nlinarith [Real.sqrt_nonneg (2 * a - 1 : ℝ), Real.sq_sqrt (show 0 ≤ (2 * a - 1 : ℝ) by linarith)]
      have h_ne3 : Real.sqrt (2 * a - 1) ≠ -Real.sqrt (2 * a - 1) := by
        intro h
        have h_eq9 : Real.sqrt (2 * a - 1) ≥ 0 := Real.sqrt_nonneg (2 * a - 1)
        have h_eq10 : Real.sqrt (2 * a - 1) + Real.sqrt (2 * a - 1) = 0 := by
          nlinarith
        have h_eq11 : Real.sqrt (2 * a - 1) = 0 := by
          nlinarith [Real.sqrt_nonneg (2 * a - 1 : ℝ)]
        nlinarith [Real.sq_sqrt (show 0 ≤ (2 * a - 1 : ℝ) by linarith), Real.sqrt_nonneg (2 * a - 1 : ℝ)]
      have h3 : (({0, Real.sqrt (2 * a - 1), -Real.sqrt (2 * a - 1)} : Set ℝ)) = ({0, Real.sqrt (2 * a - 1), -Real.sqrt (2 * a - 1)} : Set ℝ) := by rfl
      rw [Set.encard]
      simp [Set.ncard_insert_of_not_mem, h_ne1, h_ne2, h_ne3, Real.sqrt_nonneg (2 * a - 1 : ℝ)]
      all_goals
      try { tauto }
    exact h9