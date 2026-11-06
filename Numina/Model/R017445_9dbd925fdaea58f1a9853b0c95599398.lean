import Mathlib

theorem algebra_492 (x : ℝ) (a : ℝ) (hx : x ≠ 0) (h : 1 + x^2 = 2 * x * Real.cos a) :
    x^6 + 1 / x^3 = Real.cos (6 * a) + Real.cos (3 * a) := by
  have h1 : x ^ 2 - 2 * x * Real.cos a + 1 = 0 := by
    linarith
  have hcos : (x - 1 / x) ^ 2 = 0 := by 
    field_simp at h ⊢
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1 / x), sq_nonneg (x + 1 / x), sq_nonneg (x * Real.cos a), sq_nonneg (Real.cos a), Real.cos_sq_add_sin_sq a]
  have hx2 : x ^ 2 = 1 := by 
    have hne : x ≠ 0 := hx
    have eq1 : (x - 1 / x) ^ 2 = 0 := hcos
    field_simp [hne] at eq1
    nlinarith
  have hx_eq_1_or_neg1 : x = 1 ∨ x = -1 := by
    have h1 : x ^ 2 = 1 := hx2
    have : x = 1 ∨ x = -1 := by
      rw [sq_eq_one_iff] at h1
      tauto
    assumption
  have hcos_eq_1_or_neg1 : Real.cos a = 1 ∨ Real.cos a = -1 := by
    have h1 : x ^ 2 = 1 := hx2
    cases hx_eq_1_or_neg1 with
    | inl hx1 =>
      rw [hx1] at h
      have h1' : Real.cos a = 1 := by
        nlinarith
      simp [h1']
    | inr hx1 =>
      rw [hx1] at h
      have h1' : Real.cos a = -1 := by
        nlinarith
      simp [h1']
  cases hcos_eq_1_or_neg1 with
  | inl hcos1 =>
    -- Case $\cos(a) = 1$
    have hx1 : x = 1 := by
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x * Real.cos a - 1), sq_nonneg (x - 1), sq_nonneg (Real.cos a - 1)]
    rw [hx1]
    -- Show the expression equals $\cos(6a) + \cos(3a)$
    have h4 : Real.cos (6 * a) + Real.cos (3 * a) = 2 := by
      have hcos1' : Real.cos a = 1 := hcos1
      have h5 : Real.cos (3 * a) = 1 := by 
        have hcos3a : Real.cos (3 * a) = 4 * Real.cos a ^ 3 - 3 * Real.cos a := by
          rw [Real.cos_three_mul]
          <;> nlinarith
        rw [hcos3a, hcos1']
        all_goals
          nlinarith
        all_goals nlinarith
      have h6 : Real.cos (6 * a) = 1 := by
        have hcos6a : Real.cos (6 * a) = 2 * Real.cos (3 * a) ^ 2 - 1 := by
          have h1 : Real.cos (6 * a) = 2 * Real.cos (3 * a) ^ 2 - 1 := by
            rw [show 6 * a = 2 * (3 * a) by ring]
            rw [Real.cos_two_mul]
            all_goals nlinarith
          linarith
        rw [hcos6a, h5]
        all_goals
          nlinarith
      nlinarith
    norm_num [h4]
    all_goals
      nlinarith
  | inr hcos1 =>
    -- Case $\cos(a) = -1$
    have hx1 : x = -1 := by
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x * Real.cos a + 1), sq_nonneg (x + 1), sq_nonneg (Real.cos a + 1)]
    rw [hx1]
    -- Show the expression equals $\cos(6a) + \cos(3a)$
    have h4 : Real.cos (6 * a) + Real.cos (3 * a) = 0 := by
      have hcos1' : Real.cos a = -1 := hcos1
      have h5 : Real.cos (3 * a) = -1 := by 
        -- Use triple angle formula: Real.cos(3 * a) = 4 Real.cos(a)^3 - 3 Real.cos(a)
        have hcos3a : Real.cos (3 * a) = 4 * Real.cos a ^ 3 - 3 * Real.cos a := by
          rw [Real.cos_three_mul]
          <;> nlinarith
        rw [hcos3a, hcos1']
        all_goals
          nlinarith
      have h6 : Real.cos (6 * a) = 1 := by
        have hcos6a : Real.cos (6 * a) = 2 * Real.cos (3 * a) ^ 2 - 1 := by 
          have h1 : Real.cos (6 * a) = 2 * Real.cos (3 * a) ^ 2 - 1 := by
            rw [show 6 * a = 2 * (3 * a) by ring]
            rw [Real.cos_two_mul]
            all_goals nlinarith
          linarith
        rw [hcos6a, h5]
        all_goals
          nlinarith
      nlinarith
    norm_num [h4]
    all_goals
      nlinarith