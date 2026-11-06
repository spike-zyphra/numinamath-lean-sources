import Mathlib

theorem inequalities_209124 :
  {x : ℝ | x ≠ 0 ∧
    (1 / x + 1 / x ^ 3 + 1 / x ^ 5 + 1 / x ^ 7 + 1 / x ^ 9 + 1 / x ^ 11 + 1 / x ^ 13) ≤
    7 / x ^ 7}
  = {1} ∪ {x : ℝ | x < 0} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · -- Forward implication: if $x \ne 0$ and $I \le 0$, then $x = 1 \lor x < 0$.
    rintro ⟨hx, h⟩
    have h1 : x ≠ 0 := hx
    by_cases hx2 : x > 0
    · -- Assume x > 0
      have h2 : x > 0 := hx2
      have h3 : (1 / x + 1 / x ^ 3 + 1 / x ^ 5 + 1 / x ^ 7 + 1 / x ^ 9 + 1 / x ^ 11 + 1 / x ^ 13) - 7 / x ^ 7 ≤ 0 := by linarith
      have h4 : (1 / x + 1 / x ^ 3 + 1 / x ^ 5 + 1 / x ^ 7 + 1 / x ^ 9 + 1 / x ^ 11 + 1 / x ^ 13) - 7 / x ^ 7 =
          (x^12 + x^10 + x^8 - 6*x^6 + x^4 + x^2 + 1) / x^13 := by 
        have hx' : x ≠ 0 := h1 
        field_simp 
        ring
      rw [h4] at h3
      have hx4 : x ^ 13 > 0 := by positivity
      have hx5 : x^12 + x^10 + x^8 - 6*x^6 + x^4 + x^2 + 1 ≤ 0 := by 
        apply (div_nonpos_iff).mp at h3 
        cases h3 with 
        | inl h3l => nlinarith 
        | inr h3r => 
          nlinarith
      -- From inequality mn <0, need to zero. So $x=1$.
      have hx5' : (x - 1) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (x ^ 6 - 1), sq_nonneg (x ^ 5), sq_nonneg (x ^ 4 - 1), sq_nonneg (x ^ 3 - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x^2 + 1), sq_nonneg ((x - 1) * (x + 1))]
      have hx6 : x - 1 = 0 := by 
        apply pow_eq_zero 
        exact hx5' 
      have hx7 : x = 1 := by linarith 
      left 
      exact hx7
    · -- Case ¬ x > 0
      have hx2 : ¬ x > 0 := hx2
      by_cases hx3 : x < 0 
      · -- Case x < 0 
        right 
        exact hx3 
      · -- Case x ≥ 0 
        have hx3' : x ≥ 0 := by linarith 
        have hx4' : x ≤ 0 := by 
          by_contra h 
          push_neg at h 
          have hx5 : x > 0 := by linarith 
          linarith [show x > 0 by linarith, show ¬x > 0 by simpa using hx2] 
        have hx5' : x = 0 := by linarith 
        exfalso 
        tauto 
  · -- Backward implication: if $x = 1 \lor x <0$, then $x \ne 0 \land I \le 0$.
    intro h 
    rcases h with (rfl) | h 
    · -- $x = 1$ 
      constructor 
      · norm_num 
      · norm_num 
    · -- $x < 0$ 
      have h2 : x < (0 : ℝ) := h 
      constructor 
      · -- Show x ≠ 0 
        linarith 
      · -- Show the inequality 
        have h3 : (1 / x + 1 / x ^ 3 + 1 / x ^ 5 + 1 / x ^ 7 + 1 / x ^ 9 + 1 / x ^ 11 + 1 / x ^ 13) ≤ 7 / x ^ 7 := by
          have h4 : (1 / x + 1 / x ^ 3 + 1 / x ^ 5 + 1 / x ^ 7 + 1 / x ^ 9 + 1 / x ^ 11 + 1 / x ^ 13) - 7 / x ^ 7 ≤ 0 := by 
            have h5 : (1 / x + 1 / x ^ 3 + 1 / x ^ 5 + 1 / x ^ 7 + 1 / x ^ 9 + 1 / x ^ 11 + 1 / x ^ 13) - 7 / x ^ 7 = 
                (x ^ 12 + x ^ 10 + x ^ 8 - 6 * x ^ 6 + x ^ 4 + x ^ 2 + 1) / x ^ 13 := by 
                have hx' : x ≠ 0 := by linarith 
                field_simp [(show x ≠ 0 by linarith)]
                <;> ring_nf 
                <;> field_simp [(show x ≠ 0 by linarith)]
                <;> ring 
            rw [h5] 
            have hx7 : x ^ 13 < (0 : ℝ) := by
              have h8 : x < (0 : ℝ) := h2
              have : x ^ 13 < (0 : ℝ) := by
                apply Odd.pow_neg 
                · -- Show 13 is odd 
                  exact ⟨6, by norm_num⟩ 
                · -- Show x < 0 
                  linarith 
              assumption 
            have hx10 : x ^ 12 + x ^ 10 + x ^ 8 - 6 * x ^ 6 + x ^ 4 + x ^ 2 + 1 ≥ 0 := by 
              nlinarith [sq_nonneg (x ^ 6 - 1), sq_nonneg (x ^ 5), sq_nonneg (x ^ 4 - 1), sq_nonneg (x ^ 3 - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x^2 + 1), sq_nonneg ((x - 1) * (x + 1))]
            apply div_nonpos_of_nonneg_of_nonpos 
            linarith 
            all_goals 
              linarith 
          linarith 
        linarith