import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_180087 (x : ℝ) (hx : x^2 + 3 * x + 2 ≠ 0) :
    (x^2 - 3 * x + 2) / (x^2 + 3 * x + 2) ≥ 1 ↔ x < -2 ∨ x ∈ Ioc (-1) 0 := by
  constructor
  · -- Forward implication: prove that inequality holds implies the disjunction of sets.
    intro h
    have h1 : (x^2 - 3 * x + 2) / (x^2 + 3 * x + 2) - 1 ≥ 0 := by linarith
    have h2 : (x^2 - 3 * x + 2 - (x^2 + 3 * x + 2)) / (x^2 + 3 * x + 2) ≥ 0 := by
      have h12 : (x^2 - 3 * x + 2) / (x^2 + 3 * x + 2) - 1 ≥ 0 := h1
      have h3 : (x^2 - 3 * x + 2) / (x^2 + 3 * x + 2) - 1 = (x^2 - 3 * x + 2 - (x^2 + 3 * x + 2)) / (x^2 + 3 * x + 2) := by
        field_simp [(show x^2 + 3 * x + 2 ≠ 0 by assumption)]
        all_goals ring
      linarith [h3, h12]
    -- Simplify the numerator.
    have h3 : (x^2 - 3 * x + 2 - (x^2 + 3 * x + 2)) = -6 * x := by
      nlinarith
    -- Now forming h4 to simplify the expression.
    have h4 : -6 * x / (x^2 + 3 * x + 2) ≥ 0 := by
      rw [show x^2 - 3 * x + 2 - (x^2 + 3 * x + 2) = -6 * x by linarith [h3]] at h2
      exact h2
    -- Factoring the denominator.
    have h5 : x^2 + 3 * x + 2 = (x + 1) * (x + 2) := by
      nlinarith
    -- Form h7 the rewritten simplified expression.
    have h7 : -6 * x / ((x + 1) * (x + 2)) ≥ 0 := by
      rw [show (x + 1) * (x + 2) = x^2 + 3 * x + 2 by linarith [h5]]
      exact h4
    -- Now proving a contradiction with the induction hypotheses.
    by_cases h10 : x < -2
    · -- Case x ∈ (-∞, -2).
      left
      exact h10
    · -- Case x ≥ -2.
      -- Now establishing h of congruence at p back.
      have h11 : x ≥ -2 := by linarith
      -- Now proceeding to theory expansion for establishing the domain.
      -- Therefore h is : \frac{-6x}{(x+1)(x+2)} \ge 0
      -- This essentially needs cases of h positive of negatives produce is correctly side.
      have h24 : ( (x + 1) * (x + 2) > 0 ) ∨ ( (x + 1) * (x + 2) < 0 ) := by
        by_contra h
        push_neg at h
        have hc : (x + 1) * (x + 2) = 0 := by nlinarith
        have h90' : x^2 + 3 * x + 2 = 0 := by
          have h91 : x^2 + 3 * x + 2 = (x + 1) * (x + 2) := by linarith [hc]
          nlinarith
        tauto
      rcases h24 with h24 | h24
      · -- When the denominator is positive.
        have h70 : -6 * x ≥ 0 := by
          have h71 : -6 * x / ((x + 1) * (x + 2)) ≥ 0 := h7
          have hx12 : (x + 1) * (x + 2) > 0 := by nlinarith
          have h700 : -6 * x ≥ 0 := by
            apply (le_div_iff₀ (by nlinarith)).mp at h71
            linarith
          linarith
        -- Therefore x ≤ 0 and more and finally establishing properties leading up.
        have h74 : x > -1 := by
          by_contra h
          push_neg at h
          have hx36 : x ≤ -1 := by nlinarith
          have hx26 : (x + 1) * (x + 2) ≤ 0 := by
            nlinarith
          nlinarith
        have h73 : x ≤ 0 := by
          nlinarith
        have h72 : x ∈ Ioc (-1) 0 := by
          simp [Set.mem_Ioc, h74, h73]
        right
        exact h72
      · -- When the denominator is negative.
        have h70 : -6 * x ≤ 0 := by
          have h71 : -6 * x / ((x + 1) * (x + 2)) ≥ 0 := h7
          have hx12 : (x + 1) * (x + 2) < 0 := by nlinarith
          have h700 : -6 * x ≤ 0 := by
            apply (le_div_iff_of_neg' (by nlinarith)).mp at h71
            linarith
          linarith
        -- Therefore x ≥ 0 with conflict concludes.
        -- Since ((p)(q)(r)) ← contains the path.
        nlinarith
  · -- Backward implication: prove that disjunction of sets holds implies the inequality.
    intro h
    rcases h with (h10 | h10)
    · -- Case x < -2.
      have h3 : x < -2 := h10
      have h40 : (x^2 - 3 * x + 2) / (x^2 + 3 * x + 2) - 1 ≥ 0 := by
        have h5 : (x^2 - 3 * x + 2) / (x^2 + 3 * x + 2) - 1 = ( -6 * x / (x^2 + 3 * x + 2) ) := by
          field_simp [(show x^2 + 3 * x + 2 ≠ 0 by
            by_contra h14
            have h14' : x^2 + 3 * x + 2 = 0 := by linarith
            have h7' : x^2 + 3 * x + 2 = (x + 1) * (x + 2) := by ring
            rw [h7'] at h14'
            have hx5 : x = -1 ∨ x = -2 := by
              cases (mul_eq_zero.1 h14') with
              | inl h18 =>
                left; linarith
              | inr h19 =>
                right; linarith
            cases hx5 with
            | inl h97 =>
              nlinarith
            | inr h97 =>
              nlinarith
          )]
          ring
        rw [h5]
        have h60 : -6 * x / (x^2 + 3 * x + 2) ≥ 0 := by
          apply div_nonneg
          ·
            nlinarith
          all_goals
            nlinarith
        linarith
      linarith
    · -- Case x ∈ Ioc (-1) 0.
      rcases h10 with ⟨h7, h8⟩
      have h3 : x > -1 := h7
      have h4 : x ≤ 0 := by linarith
      have h40 : (x^2 - 3 * x + 2) / (x^2 + 3 * x + 2) - 1 ≥ 0 := by
        have h5 : (x^2 - 3 * x + 2) / (x^2 + 3 * x + 2) - 1 = ( -6 * x / (x^2 + 3 * x + 2) ) := by
          field_simp [(show x^2 + 3 * x + 2 ≠ 0 by
            by_contra h17
            have h17' : x^2 + 3 * x + 2 = 0 := by linarith
            have h7' : x^2 + 3 * x + 2 = (x + 1) * (x + 2) := by ring
            rw [h7'] at h17'
            have hx5 : x = -1 ∨ x = -2 := by
              cases (mul_eq_zero.1 h17') with
              | inl h18 =>
                left; linarith
              | inr h19 =>
                right; linarith
            cases hx5 with
            | inl h97 =>
              nlinarith
            | inr h97 =>
              nlinarith
          )]
          ring
        rw [h5]
        have h60 : -6 * x / (x^2 + 3 * x + 2) ≥ 0 := by
          apply div_nonneg
          ·
            nlinarith
          all_goals
            nlinarith
        linarith
      linarith