import Mathlib

open Real Set

theorem inequalities_5564 (t : ℝ) :
    (∀ a b : ℝ, a ∈ Icc 1 2 → b ∈ Icc 1 2 → a^2 + b^2 ≥ (5 - 2 * t) * a + t * b) ↔ t ≥ 4 := by
        constructor
        · -- Assume that inequality holds for all a, b ∈ [1, 2], we need to prove t ≥ 4
            intro h
            by_contra ht
            push_neg at ht
            by_cases h' : t ≥ 2
            · -- Case where t ≥ 2
                have h1 := h 1 (0.5 * t) (by norm_num) (by
                    constructor <;> nlinarith
                )
                nlinarith
            · -- Case where t < 2
                have h1 := h 1 1 (by norm_num) (by norm_num)
                nlinarith
        · -- Now prove the reverse direction: if t ≥ 4, then inequality holds for all a, b ∈ [1, 2]
            intro ht a b ha hb
            have ha1 : 1 ≤ a := by
                simpa using ha.left
            have ha2 : a ≤ 2 := by
                simpa using ha.right
            have hb1 : 1 ≤ b := by
                simpa using hb.left
            have hb2 : b ≤ 2 := by
                simpa using hb.right
            nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b), sq_nonneg (t - 4)]