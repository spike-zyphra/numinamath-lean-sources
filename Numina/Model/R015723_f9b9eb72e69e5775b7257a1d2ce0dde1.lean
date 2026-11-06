import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_235883 {f : ℝ → ℝ} (hf : ∀ x y, x < y → f x > f y)
  (x : ℝ) (hx : x ≠ 0) : f (abs (1 / x)) < f 1 ↔ x ∈ Ioo (-1) 0 ∪ Ioo 0 1 := by
  constructor
  · -- Forward direction: $f(\lvert \frac{1}{x} \rvert) < f(1) \implies x \in (-1,0) \cup (0,1)$
    intro h
    have h1 : abs (1 / x) > 1 := by
      by_contra h2
      push_neg at h2
      -- Now `abs (1 / x) ≤ 1`.
      -- We need to show this implies $f (abs (1 / x)) \ge f 1$, which would contradict h: f (abs (1 / x)) < f 1.
      -- Consider two cases: $abs (1 / x) < 1$ and $abs (1 / x) = 1$.
      by_cases h4 : abs (1 / x) < (1 : ℝ)
      · -- Case 1: abs (1 / x) < 1.
        -- From hf: since abs (1 / x) < 1, we have f (abs (1 / x)) > f 1.
        have h5 : f (abs (1 / x)) > f 1 := by
          apply hf
          all_goals linarith
        linarith -- Creates a contradiction from h5 (f |1/x| > f 1) and h (f |1/x| < f 1).
      · -- Case 2: abs (1 / x) ≥ 1. But with h2: abs (1/x) ≤1, we get abs (1/x) =1.
        have h6 : abs (1 / x) = (1 : ℝ) := by linarith
        -- Substitute h6 into h, which is `f (abs (1 / x)) < f 1`.
        rw [h6] at h
        -- Now we have f 1 < f 1, which is a contradiction.
        all_goals linarith
    have h2 : x > -1 ∧ x < 0 ∨ x > 0 ∧ x < 1 := by
      cases' abs_cases (1 / x) with h3 h3
      · -- Case 1: 1 / x ≥ 0, so abs (1 / x) = 1 / x > 1
        have h4 : x > 0 := by
          by_contra h5
          push_neg at h5
          have h6 : (1 / x) ≤ 0 := by
            have h7 : x ≤ 0 := by linarith
            have h8 : x < (0 : ℝ) := by
              by_contra h9
              push_neg at h9
              have h10 : x = 0 := by linarith
              tauto
            have h9 : (1 / x) ≤ 0 := by
              apply div_nonpos_of_nonneg_of_nonpos
              all_goals
                try { linarith }
                all_goals try { tauto }
            nlinarith
          nlinarith
          all_goals try { linarith }
          all_goals try { tauto }
        have h5 : x < 1 := by
          by_contra h6
          push_neg at h6
          have h7 : (1 / x) ≤ (1 : ℝ) := by
            apply (div_le_iff₀ (by linarith)).mpr
            all_goals
              nlinarith
              all_goals try { tauto }
          nlinarith
          all_goals try { linarith
          }
          all_goals try { tauto }
        right
        exact ⟨h4, h5⟩
      · -- Case 2: 1 / x < 0, so abs (1 / x) = - (1 / x) > 1
        have h8 : x < 0 := by
          by_contra h9
          push_neg at h9
          have h9 : x ≥ 0 := by linarith
          have h10 : (1 / x) ≥ 0 := by
            apply div_nonneg
            norm_num
            all_goals
              try { linarith }
              all_goals try { tauto }
          nlinarith
          all_goals try { linarith
          }
          all_goals try { tauto }
        have h9 : x > -1 := by
          by_contra h10
          push_neg at h10
          have h11 : x ≤ (-1 : ℝ) := by linarith
          have h12 : (1 / x) ≥ -1 := by
            have h13 : x ≤ (-1 : ℝ) := by linarith
            have h14 : (1 / x) ≥ -1 := by
              apply (le_div_iff_of_neg' (by linarith)).mpr
              all_goals nlinarith
            nlinarith
            all_goals try { linarith
            }
          nlinarith
          all_goals try { linarith }
        left
        exact ⟨h9, h8⟩
    cases h2 with
    | inl h3 =>
      left
      exact ⟨h3.1, h3.2⟩
    | inr h3 =>
      right
      exact ⟨h3.1, h3.2⟩
  · -- Backward direction: $x \in (-1,0) \cup (0,1) \implies f(\lvert \frac{1}{x} \rvert) < f(1)$
    intro h
    rcases h with (h | h)
    · -- Case x ∈ (-1, 0)
      rcases h with ⟨h1, h2⟩
      have h3 : abs (1 / x) > (1 : ℝ) := by
        have h4 : 1 / x < (0 : ℝ) := by
          apply div_neg_of_pos_of_neg
          all_goals linarith
        have h5 : abs (1 / x) = - (1 / x) := by
          rw [abs_of_neg h4]
        have h6 : - (1 / x) > (1 : ℝ) := by
          have h7 : 1 / x < (-1 : ℝ) := by
            have hx1 : x < (0 : ℝ) := by linarith [h2]
            have hx2 : x > (-1 : ℝ) := by linarith [h1]
            apply (div_lt_iff_of_neg (by linarith)).mpr
            nlinarith
          linarith
        rw [h5]
        all_goals linarith
      have h4 : f (abs (1 / x)) < f 1 := by
        have h5 : abs (1 / x) > (1 : ℝ) := h3
        have h6 : 1 < abs (1 / x) := by linarith
        have h7 : f 1 > f (abs (1 / x)) := by
          apply hf
          all_goals nlinarith
        linarith
      linarith
    · -- Case x ∈ (0, 1)
      rcases h with ⟨h1, h2⟩
      have h3 : abs (1 / x) > (1 : ℝ) := by
        have h4 : 1 / x > (0 : ℝ) := by
          apply div_pos
          norm_num
          all_goals linarith
        have h5 : abs (1 / x) = 1 / x := by
          rw [abs_of_pos h4]
        have h6 : 1 / x > (1 : ℝ) := by
          have hx1 : x > (0 : ℝ) := by linarith [h1]
          have hx2 : x < (1 : ℝ) := by linarith [h2]
          have h7 : 1 / x > (1 : ℝ) := by
            apply (lt_div_iff₀ (by linarith)).mpr
            nlinarith
            all_goals try linarith
          assumption
        rw [h5]
        all_goals linarith
      have h4 : f (abs (1 / x)) < f 1 := by
        have h5 : abs (1 / x) > (1 : ℝ) := h3
        have h6 : 1 < abs (1 / x) := by linarith
        have h7 : f 1 > f (abs (1 / x)) := by
          apply hf
          all_goals nlinarith
        linarith
      linarith