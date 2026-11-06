import Mathlib

theorem algebra_76481 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a ^ 2 + b + c = 1 / a) (h2 : b ^ 2 + c + a = 1 / b) (h3 : c ^ 2 + a + b = 1 / c) :
    a = b ∨ b = c ∨ a = c := by
  have eq1 : a^3 + a * b + a * c = 1 := by
    have h11 : a ^ 2 + b + c = 1 / a := h1
    field_simp at h11 ⊢
    nlinarith [sq_pos_of_ne_zero ha]
  have eq2 : b^3 + b * c + b * a = 1 := by
    have h22 : b ^ 2 + c + a = 1 / b := h2
    field_simp at h22 ⊢
    nlinarith [sq_pos_of_ne_zero hb]
  have eq3 : c^3 + c * a + c * b = 1 := by
    have h33 : c ^ 2 + a + b = 1 / c := h3
    field_simp at h33 ⊢
    nlinarith [sq_pos_of_ne_zero hc]
  -- Now, perform the main case analysis
  by_cases h4 : a = b
  · -- Case where a = b
    left
    exact h4
  · -- Case where ¬a = b
    by_cases h5 : b = c
    · -- Case where b = c
      right
      left
      exact h5
    · -- Case where ¬b = c
      by_cases h6 : a = c
      · -- Case where a = c
        right
        right
        exact h6
      · -- Case where ¬a = c
        -- We have ¬a = b, ¬b = c, ¬a = c
        -- From eq1, eq2: a^3 + a * b + a * c = 1 and b^3 + b * c + b * a = 1
        -- Subtract these => (a^3 - b^3) + (a * b - b * a) + (a * c - b * c) = 0
        -- simplifying => (a-b)(a^2 + ab + b^2) + (a-b)c = 0
        -- simplifying => (a-b)(a^2 + ab + b^2 + c) = 0
        have h4' : a ^ 2 + a * b + b ^ 2 + c = 0 := by
          have eq1' : a ^ 3 + a * b + a * c = 1 := eq1
          have eq2' : b ^ 3 + b * c + b * a = 1 := eq2
          have h7 : a ^ 3 + a * b + a * c - (b ^ 3 + b * c + b * a) = 0 := by linarith
          have h7' : (a - b) * (a ^ 2 + a * b + b ^ 2 + c) = 0 := by
            nlinarith
          cases' (mul_eq_zero.1 h7') with h9 h10
          · -- Case a - b = 0
            exfalso
            exact h4 (by linarith)
          · -- Case a^2 + ab + b^2 + c = 0
            linarith
        -- From eq2, eq3: b^3 + b * c + b * a = 1 and c^3 + c * a + c * b = 1
        -- Subtract these => (b^3 - c^3) + (b * a - c * a) + (b * c - c * b) = 0
        -- simplifying => (b-c)(b^2 + bc + c^2) + (b-c)a = 0
        -- simplifying => (b-c)(b^2 + bc + c^2 + a) = 0
        have eq5 : b ^ 2 + b * c + c ^ 2 + a = 0 := by
          have eq2' : b^3 + b * c + b * a = 1 := eq2
          have eq3' : c^3 + c * a + c * b = 1 := eq3
          have h9 : b^3 + b * c + b * a - (c^3 + c * a + c * b) = 0 := by linarith
          have h9' : b ^ 3 + b * c + b * a = c ^ 3 + c * a + c * b := by linarith
          have h7' : (b - c) * (b ^ 2 + b * c + c ^ 2 + a) = 0 := by
            nlinarith
          cases' (mul_eq_zero.1 h7') with h9 h9
          · -- Case b - c = 0
            exfalso
            exact h5 (by linarith)
          · -- Case b^2 + bc + c^2 + a = 0
            linarith
        -- Goal now is a = b ∨ b = c ∨ a = c
        -- We have ¬a = b (from `h4`), ¬b = c (from `h5`), and ¬a = c (from `h6`)
        -- The only way to satisfy the goal is with a = b ∨ b = c ∨ a = c
        -- But all are negated. So we need to show False.
        exfalso
        -- From h4' and eq5 (and others) we need to deduce `False`
        nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_pos_of_ne_zero (show (a - b) ≠ 0 by intro h'; apply h4; linarith), sq_pos_of_ne_zero (show (b - c) ≠ 0 by intro h'; apply h5; linarith), sq_pos_of_ne_zero (show (a - c) ≠ 0 by intro h'; apply h6; linarith), mul_self_nonneg (a * b), mul_self_nonneg (a * c), mul_self_nonneg (b * c)]