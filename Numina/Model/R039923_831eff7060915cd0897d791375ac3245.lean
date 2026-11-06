import Mathlib

theorem algebra_315119 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : 1 / a + 1 / b + 1 / c = 1 / (a + b + c)) :
    ∃ x y, x = -y ∧ (x = a ∧ y = b ∨ x = a ∧ y = c ∨ x = b ∧ y = c) := by
  by_cases h1 : a + b + c = 0
  · -- If a + b + c = 0, the hypothesis leads to a contradiction
    have h2 : 1 / (a + b + c) = 0 := by
      rw [h1]
      norm_num
    -- The original hypothesis becomes 1/a +1/b +1/c =0
    have h3 : 1 / a + 1 / b + 1 / c = 0 := by
      linarith [h, h2]
    have h4 : a * b + a * c + b * c = 0 := by
      have h4 : 1 / a + 1 / b + 1 / c = (b * c + a * c + a * b) / (a * b * c) := by
        field_simp
        <;> ring
      rw [h4] at h3
      have h5 : a * b * c ≠ 0 := by
        apply mul_ne_zero
        apply mul_ne_zero
        exact ha
        exact hb
        exact hc
      field_simp [h5] at h3 ⊢
      nlinarith
    -- Substitute c = -a -b into the equation.
    have h5 : c = -a - b := by linarith
    rw [show c = -a - b by linarith [h5]] at h4
    -- This implies that a² + ab + b² =0
    have h7 : a ^ 2 + a * b + b ^ 2 = 0 := by
      nlinarith
    -- This is impossible because a and b are non-zero
    have h8 : a ^ 2 + a * b + b ^ 2 > 0 := by
      nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_nonneg (a + b / 2), sq_nonneg (b)]
    nlinarith
  · -- Assume that a + b + c ≠ 0, we can clear the denominators.
    have h1 : a + b + c ≠ 0 := h1
    have eq1 : 1 / a + 1 / b + 1 / c = 1 / (a + b + c) := h
    -- Multiply both sides by a * b * c * (a + b + c) to clear denominators.
    have h2 : b * c * (a + b + c) + a * c * (a + b + c) + a * b * (a + b + c) = a * b * c := by
      have h3 : a + b + c ≠ 0 := h1
      field_simp [ha, hb, hc, h3] at eq1 ⊢
      nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_pos_of_ne_zero h3, sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c)]
    -- Rearrange the equation to show that it factors.
    have h3 : (a + b) * (a + c) * (b + c) = 0 := by 
      nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c), sq_pos_of_ne_zero h1]
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Case (a + b) * (a + c) = 0
      cases' (mul_eq_zero.mp h4) with h6 h7
      · -- Case a + b = 0
        have h7 : a + b = 0 := by
          linarith
        have h8 : a = -b := by
          linarith
        use a, b
        constructor
        · -- Show that a = -b
          linarith
        · -- Show that either (a = a ∧ b = b) or similar
          left
          constructor
          · -- Show that a = a
            rfl
          · -- Show that b = b
            rfl
      · -- Case a + c = 0
        have h8 : a + c = 0 := by
          linarith
        have h9 : a = -c := by
          linarith
        use a, c
        constructor
        · -- Show that a = -c
          linarith
        · -- Show that either (a = a ∧ c = b) or similar
          right
          left
          constructor
          · -- Show that a = a
            rfl
          · -- Show that c = b
            linarith
    · -- Case b + c = 0
      have h10 : b + c = 0 := by
        linarith
      have h11 : b = -c := by
        linarith
      use b, c
      constructor
      · -- Show that b = -c
        linarith
      · -- Show that either (b = a ∧ c = c) or similar
        right
        right
        constructor
        · -- Show that b = a
          linarith
        · -- Show that c = c
          rfl