import Mathlib

theorem number_theory_208345 (x y : ℤ) : x^2 * y = 10000 * x + y ↔
    (x = -9 ∧ y = -1125) ∨ (x = -3 ∧ y = -3750) ∨ (x = 0 ∧ y = 0) ∨
    (x = 3 ∧ y = 3750) ∨ (x = 9 ∧ y = 1125) := by
  constructor
  · -- Assume x^2 * y = 10000 * x + y, prove the disjunction of the possible pairs
    rintro h
    have h1 : y * (x ^ 2 - 1) = 10000 * x := by
      nlinarith
    by_cases h2 : x ^ 2 - 1 = 0
    · -- x^2 - 1 = 0
      have h3 : x ^ 2 = 1 := by
        nlinarith
      have h4 : x = 1 ∨ x = -1 := by
        rw [sq_eq_one_iff] at h3
        exact h3
      rcases h4 with (r | r)
      · -- x = 1
        rw [show x = 1 by linarith] at h1
        exfalso
        norm_num at h1
      · -- x = -1
        rw [show x = -1 by linarith] at h1
        exfalso
        norm_num at h1
    · -- x^2 - 1 ≠ 0
      have h3 : x ^ 2 - 1 ≠ 0 := h2
      have h4 : (x ^ 2 - 1) ∣ 10000 * x := by
        use y
        all_goals
          linarith
      have h5 : x ≤ 100 := by
        by_contra h
        push_neg at h
        have h7 : (x ^ 2 - 1) ∣ 10000 := by
          have h8 : (x ^ 2 - 1) ∣ 10000 * x := h4
          have h9 : IsCoprime (x ^ 2 - 1) x := by
            show IsCoprime (x ^ 2 - 1) x
            use -1
            use x
            nlinarith
          have h10 : (x ^ 2 - 1) ∣ 10000 := by
            have h11 : (x ^ 2 - 1) ∣ 10000 * x := h4
            have h12 : (x ^ 2 - 1) ∣ 10000 := by
              have h13 : (x ^ 2 - 1) ∣ 10000 * x := h11
              have h14 : (x ^ 2 - 1) ∣ 10000 := by
                have h15 : IsCoprime (x ^ 2 - 1) x := h9
                exact IsCoprime.dvd_of_dvd_mul_right h15 h13
              exact h14
            exact h12
          exact h10
        have h8 : (x ^ 2 - 1) ≤ 10000 := by
          exact Int.le_of_dvd (show 0 < (10000 : ℤ) by norm_num) h7
        nlinarith [sq_nonneg (x), sq_nonneg (x - 100)]
      have h6 : x ≥ -100 := by
        by_contra h
        push_neg at h
        have h7' : (x ^ 2 - 1) ∣ 10000 := by
          have h8 : (x ^ 2 - 1) ∣ 10000 * x := h4
          have h9 : IsCoprime (x ^ 2 - 1) x := by
            show IsCoprime (x ^ 2 - 1) x
            use -1
            use x
            nlinarith
          have h10 : (x ^ 2 - 1) ∣ 10000 := by
            have h11 : (x ^ 2 - 1) ∣ 10000 * x := h4
            have h12 : (x ^ 2 - 1) ∣ 10000 := by
              have h13 : (x ^ 2 - 1) ∣ 10000 * x := h11
              have h14 : (x ^ 2 - 1) ∣ 10000 := by
                have h15 : IsCoprime (x ^ 2 - 1) x := h9
                exact IsCoprime.dvd_of_dvd_mul_right h15 h13
              exact h14
            exact h12
          exact h10
        have h8 : (x ^ 2 - 1) ≤ 10000 := by
          exact Int.le_of_dvd (show 0 < (10000 : ℤ) by norm_num) h7'
        nlinarith [sq_nonneg (x), sq_nonneg (x + 100)]
      interval_cases x <;> omega
  · -- Assume the disjunction of the possible pairs, prove x^2 * y = 10000 * x + y
    rintro (h | h | h | h | h)
    · -- Case (-9, -1125)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Case (-3, -3750)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Case (0, 0)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Case (3, 3750)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Case (9, 1125)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num