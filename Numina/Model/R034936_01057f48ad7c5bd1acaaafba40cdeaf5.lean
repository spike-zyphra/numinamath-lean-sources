import Mathlib

theorem algebra_191902 :
  {(x, y) : ℝ × ℝ | x ≠ 0 ∧ y ≠ 0 ∧ x ^ 2 / y + y ^ 2 / x = 12 ∧ 1 / x + 1 / y = 1 / 3} =
  {(6, 6), ((-3 + 3 * Real.sqrt 5) / 2, (-3 - 3 * Real.sqrt 5) / 2), ((-3 - 3 * Real.sqrt 5) / 2, (-3 + 3 * Real.sqrt 5) / 2)} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.forall, Prod.mk.injEq]
  constructor
  · -- First direction: if (x,y) satisfies the system, then it's one of the solutions.
    rintro ⟨hx, hy, h1, h2⟩

    have h3 : x * y - 3 * (x + y) = 0 := by
      field_simp at h2
      nlinarith

    have h4 : (x ^ 3 + y ^ 3 : ℝ) = 12 * (x * y : ℝ) := by
      have h6 : x ^ 2 / y + y ^ 2 / x = 12 := h1
      have h7 : x ^ 2 / y + y ^ 2 / x = (x ^ 3 + y ^ 3) / (x * y) := by
        field_simp
        ring
      rw [h7] at h6
      have h8 : (x * y : ℝ) ≠ 0 := by
        apply mul_ne_zero
        exact hx
        exact hy
      field_simp at h6 ⊢
      nlinarith

    have h10 : x ^ 3 + y ^ 3 = 36 * (x + y : ℝ) := by
      have h11 : x * y = 3 * (x + y : ℝ) := by
        nlinarith [h3]
      have h12 : x ^ 3 + y ^ 3 = 12 * (x * y : ℝ) := h4
      rw [h11] at h12
      linarith

    have h11 : (x + y : ℝ) * ((x + y : ℝ) ^ 2 - 3 * (x * y : ℝ) - 36) = 0 := by
      have eq1 : x ^ 3 + y ^ 3 = (x + y : ℝ) ^ 3 - 3 * (x * y : ℝ) * (x + y : ℝ) := by
        ring
      have eq2 : x ^ 3 + y ^ 3 = 36 * (x + y : ℝ) := h10
      nlinarith

    cases' (mul_eq_zero.1 h11) with h13 h14
    · -- Case where x + y = 0
      have h15 : x + y = 0 := by
        nlinarith
      have h16 : x * y = 0 := by
        nlinarith [h3, h15]
      cases' (mul_eq_zero.1 h16) with h18 h19
      · -- x = 0
        exfalso
        exact hx (by linarith)
      · -- y = 0
        exfalso
        exact hy (by linarith)
    · -- Case where (x + y)^2 - 3xy - 36 = 0
      have h17 : ((x + y : ℝ) : ℝ) ^ 2 - 9 * (x + y : ℝ) - 36 = 0 := by
        have h18 : x * y = 3 * (x + y : ℝ) := by
          nlinarith [h3]
        rw [h18] at h14
        nlinarith

      have h18 : ((x + y : ℝ) - 12) * ((x + y : ℝ) + 3) = 0 := by
        nlinarith

      cases' (mul_eq_zero.1 h18) with h19 h20
      · -- Case h19
        have h21 : x + y = 12 := by linarith
        have h22 : x * y = 36 := by
          nlinarith [h3, h21]
        have h23 : (x - 6) ^ 2 = 0 := by
          have h27 : (y) = 12 - x := by linarith
          rw [show y = 12 - x by linarith] at h22
          nlinarith
        have h31 : x - 6 = 0 := by
          nlinarith
        have h32 : x = 6 := by linarith
        have h33 : y = 6 := by linarith
        simp [h32, h33]
      · -- Case h20
        have h21 : x + y = -3 := by linarith
        have h22 : x * y = -9 := by
          nlinarith [h3, h21]
        have h23 : y = -3 - x := by linarith
        rw [show y = -3 - x by linarith] at h22
        have h24 : x ^ 2 + 3 * x - 9 = 0 := by
          nlinarith
        have h26 : (x - (-3 + 3 * Real.sqrt 5) / 2) * (x - (-3 - 3 * Real.sqrt 5) / 2) = 0 := by
          nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
        cases' (mul_eq_zero.1 h26) with h27 h28
        · -- When h27 = 0
          have hx1 : x = (-3 + 3 * Real.sqrt 5) / 2 := by nlinarith
          have hy1 : y = (-3 - 3 * Real.sqrt 5) / 2 := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num : (5 : ℝ) > 0), Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
          simp [hx1, hy1]
        · -- When h28 = 0
          have hx2 : x = (-3 - 3 * Real.sqrt 5) / 2 := by nlinarith
          have hy2 : y = (-3 + 3 * Real.sqrt 5) / 2 := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num : (5 : ℝ) > 0), Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num : (5 : ℝ) ≥ 0)]
          simp [hx2, hy2]

  · -- Proof of the second direction.
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ )
    · -- First solution (6,6).
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Second solution.
      constructor
      · -- Show x ≠ 0.
        have h3 : Real.sqrt 5 > 1 := by
          have h4 : Real.sqrt 5 > Real.sqrt 1 := by
            apply Real.sqrt_lt_sqrt
            all_goals norm_num
          have h5 : Real.sqrt 1 = 1 := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          nlinarith
        have h8 : (-3 + 3 * Real.sqrt 5 : ℝ) ≠ 0 := by
          by_contra h
          have h9 : Real.sqrt 5 = 1 := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          have h10 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
          have h11 : (Real.sqrt 5) ^ 2 = 1 := by
            rw [h9]
            norm_num
          nlinarith
        intro h
        apply h8
        linarith
      constructor
      · -- Show y ≠ 0.
        have h3 : Real.sqrt 5 > 0 := by
          positivity
        have h8 : (-3 - 3 * Real.sqrt 5 : ℝ) ≠ 0 := by
          by_contra h
          have h3 : Real.sqrt 5 > 0 := by
            positivity
          have h9 : Real.sqrt 5 = -1 := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
        intro h
        apply h8
        linarith
      constructor
      · -- Show h1 = 12.
        have h3 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
        field_simp [(show (-3 + 3 * Real.sqrt 5 : ℝ) ≠ 0 by
          by_contra h
          have h9 : Real.sqrt 5 = 1 := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          have h10 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
          have h11 : (Real.sqrt 5) ^ 2 = 1 := by
            rw [h9]
            norm_num
          nlinarith
        ), (show (-3 - 3 * Real.sqrt 5 : ℝ) ≠ 0 by
          by_contra h
          have h3 : Real.sqrt 5 > 0 := by
            positivity
          have h9 : Real.sqrt 5 = -1 := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
        )]
        nlinarith [sq_pos_of_pos (show Real.sqrt 5 > 0 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 ^ 2 - 5)]
      · -- Show h2 = 1/3.
        field_simp [(show (-3 + 3 * Real.sqrt 5 : ℝ) ≠ 0 by
          by_contra h
          have h9 : Real.sqrt 5 = 1 := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          have h10 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
          have h11 : (Real.sqrt 5) ^ 2 = 1 := by
            rw [h9]
            norm_num
          nlinarith
        ), (show (-3 - 3 * Real.sqrt 5 : ℝ) ≠ 0 by
          by_contra h
          have h3 : Real.sqrt 5 > 0 := by
            positivity
          have h9 : Real.sqrt 5 = -1 := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
        )]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    · -- Third solution.
      constructor
      · -- Show x ≠ 0.
        have h3 : Real.sqrt 5 > 0 := by
          positivity
        have h8 : (-3 - 3 * Real.sqrt 5 : ℝ) ≠ 0 := by
          by_contra h
          have h3 : Real.sqrt 5 > 0 := by
            positivity
          have h9 : Real.sqrt 5 = -1 := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
        intro h
        apply h8
        linarith
      constructor
      · -- Show y ≠ 0.
        have h8 : (-3 + 3 * Real.sqrt 5 : ℝ) ≠ 0 := by
          by_contra h
          have h9 : Real.sqrt 5 = 1 := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          have h10 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
          have h11 : (Real.sqrt 5) ^ 2 = 1 := by
            rw [h9]
            norm_num
          nlinarith
        intro h
        apply h8
        linarith
      constructor
      · -- Show h1 = 12.
        have h3 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
        field_simp [(show (-3 - 3 * Real.sqrt 5 : ℝ) ≠ 0 by
          by_contra h
          have h3 : Real.sqrt 5 > 0 := by
            positivity
          have h9 : Real.sqrt 5 = -1 := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
        ), (show (-3 + 3 * Real.sqrt 5 : ℝ) ≠ 0 by
          by_contra h
          have h9 : Real.sqrt 5 = 1 := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          have h10 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
          have h11 : (Real.sqrt 5) ^ 2 = 1 := by
            rw [h9]
            norm_num
          nlinarith
        )]
        nlinarith [sq_pos_of_pos (show Real.sqrt 5 > 0 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 ^ 2 - 5)]
      · -- Show h2 = 1/3.
        field_simp [(show (-3 - 3 * Real.sqrt 5 : ℝ) ≠ 0 by
          by_contra h
          have h3 : Real.sqrt 5 > 0 := by
            positivity
          have h9 : Real.sqrt 5 = -1 := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
        ), (show (-3 + 3 * Real.sqrt 5 : ℝ) ≠ 0 by
          by_contra h
          have h9 : Real.sqrt 5 = 1 := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          have h10 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
          have h11 : (Real.sqrt 5) ^ 2 = 1 := by
            rw [h9]
            norm_num
          nlinarith
        )]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]