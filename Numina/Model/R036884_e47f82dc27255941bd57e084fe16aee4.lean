import Mathlib

open BigOperators Real

theorem algebra_12221 :
  IsGreatest {M | ∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → a + b > c → b + c > a → c + a > b → (a^2 + b^2)/c^2 > M} (1/2) := by
  constructor
  · -- Show that 1/2 is in the set
    intro a b c ha hb hc h1 h2 h3
    have h4 : 0 < c ^ 2 := by nlinarith
    have h5 : 2 * (a ^ 2 + b ^ 2) > c ^ 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b)]
    have h6 : (a ^ 2 + b ^ 2) / c ^ 2 > 1 / 2 := by
      have h7 : 0 < c ^ 2 := by positivity
      apply (lt_div_iff₀ (by positivity)).mpr
      nlinarith
    linarith
  · -- Show that 1/2 is the greatest element.
    intro M hM
    have h8 : ∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → a + b > c → b + c > a → c + a > b → (a^2 + b^2)/c^2 > M := hM
    by_contra h
    push_neg at h
    have h10 : M > (1 / 2 : ℝ) := by linarith
    -- Find a contradiction with the previous statement.
    -- We constructed a triangle with side lengths 1, 1, sqrt(2 / M).
    have ha2 : (1 : ℝ) > 0 := by norm_num
    have hb2 : (1 : ℝ) > 0 := by norm_num
    have hc2' : Real.sqrt (2 / M) > 0 := by
      have h48 : M > 0 := by linarith [h10]
      have h49 : (2 / M : ℝ) > 0 := by
        apply div_pos
        all_goals linarith
      have h50 : Real.sqrt (2 / M) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith [h49]
      exact h50
    have hc3 : (1 : ℝ) + (1 : ℝ) > Real.sqrt (2 / M) := by
      have hc_ineq : Real.sqrt (2 / M) < (2 : ℝ) := by
        have h42a : M > 1 / 2 := h10
        have h47b : (2 / M : ℝ) < (4 : ℝ) := by
          have h9 : M > 1 / 2 := h42a
          have h43 : M > 0 := by linarith
          apply (div_lt_iff₀ (show (0 : ℝ) < M by linarith)).mpr
          nlinarith
        have h47c : Real.sqrt (2 / M) < (2 : ℝ) := by
          have h3' : (Real.sqrt (2 / M) : ℝ) ^ 2 < (4 : ℝ) := by
            have h21' : (Real.sqrt (2 / M) : ℝ) ^ 2 = (2 / M : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 2 / M by
              have h9 : M > 1 / 2 := h10
              have h9' : M > 0 := by linarith
              positivity
            )
            nlinarith
          have h58 : Real.sqrt (2 / M) < (2 : ℝ) := by
            nlinarith [Real.sqrt_nonneg (2 / M : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 / M : ℝ) by
              have h9 : M > 1 / 2 := h10
              have h9' : M > 0 := by linarith
              positivity
            ), sq_nonneg (Real.sqrt (2 / M) - 2)]
          exact h58
        exact h47c
      have hc_ineq' : Real.sqrt (2 / M) < (2 : ℝ) := hc_ineq
      nlinarith [Real.sqrt_nonneg (2 / M : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 / M : ℝ) by
        have h9 : M > 1 / 2 := h10
        have h9' : M > 0 := by linarith
        positivity
      ), hc_ineq']
    -- Show the second triangle inequality.
    have hb4 : (1 : ℝ) + Real.sqrt (2 / M) > (1 : ℝ) := by
      have h14 : Real.sqrt (2 / M) > 0 := hc2'
      nlinarith
    -- Show the third triangle inequality.
    have ha5 : Real.sqrt (2 / M) + (1 : ℝ) > (1 : ℝ) := by
      have h14 : Real.sqrt (2 / M) > 0 := hc2'
      nlinarith
    -- Our set hypothesis think this should be greater.
    have h40 : (1^2 + 1^2) / (Real.sqrt (2 / M)) ^ 2 > M := by
      apply h8 1 1 (Real.sqrt (2 / M))
      all_goals
      try exact ha2
      try exact hb2
      try exact hc2'
      try exact hc3
      try exact hb4
      try exact ha5
    -- But we constructed it to be less.
    have h41 : (1^2 + 1^2) / (Real.sqrt (2 / M)) ^ 2 ≤ (M : ℝ) := by
      have h41 : (Real.sqrt (2 / M)) ^ 2 = (2 / M : ℝ) := Real.sq_sqrt (by
        have h9 : M > 1 / 2 := h10
        have h9' : M > 0 := by linarith
        positivity
      )
      rw [h41]
      field_simp at *
      all_goals
      nlinarith
    -- Contradicts our hypothesis
    linarith