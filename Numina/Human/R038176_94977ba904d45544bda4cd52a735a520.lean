import Mathlib

/- 6. Real numbers $a, b, c, d$ satisfy the equation $a b + b c + c d + d a = 16$.

a) Prove that among the numbers $a, b, c, d$, there are two with a sum of at most 4.

b) What is the minimum value that the sum $a^{2} + b^{2} + c^{2} + d^{2}$ can have? -/
theorem algebra_259807 (a b c d : ℝ) (h : a * b + b * c + c * d + d * a = 16) :
    (a + b ≤ 4 ∨ a + c ≤ 4 ∨ a + d ≤ 4 ∨ b + c ≤ 4 ∨ b + d ≤ 4 ∨ c + d ≤ 4) ∧
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ 16 := by

        --Factorizing a * b + b * c + c * d + d * a gives...
        have h1 : (a + c) * (b + d) = 16 := by
            rw [←h]; ring
        --Prove (a + c ≤ 4) ∨ (b + d ≤ 4) by contradiction.
        have h2 : (a + c ≤ 4) ∨ (b + d ≤ 4) := by
            by_contra h_or
            push_neg at h_or
            have h2_1 : 4 < a + c := by exact h_or.1
            have h2_2 : 4 < b + d := by exact h_or.2

            have h2_3 : 16 < (a + c) * (b + d) := by
                conv_lhs =>
                    calc (16:ℝ)
                    _ = 4 * 4 := by norm_num
                apply mul_lt_mul_of_pos <;> linarith

            rw [h1] at h2_3
            exact (lt_self_iff_false 16).mp h2_3

        --First part is done.
        have h_part1 : a + b ≤ 4 ∨ a + c ≤ 4 ∨ a + d ≤ 4 ∨ b + c ≤ 4 ∨ b + d ≤ 4 ∨ c + d ≤ 4 := by
            cases h2 with
            | inl h_ac => exact Or.inr (Or.inl h_ac)
            | inr h_bd => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_bd))))

        have h_part2 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ 16 := by
            have h3 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 =
                        1 / 2 * (a - b)^2 + 1/2 * (b - c)^2 + 1/2 * (c - d)^2 + 1 / 2 * (d - a)^2 + a * b + b * c + c * d + d * a := by
                            ring

            --Prove each of the following inequalities separately.
            have h30 : 1 / 2 * (a - b)^2 + a * b ≥ a * b := by
                have : 1/ 2 * (a - b)^2 ≥ 0 := by
                    apply mul_nonneg
                    · norm_num -- proves 1/2 ≥ 0
                    · apply pow_two_nonneg -- proves (a - b)^2 ≥ 0
                exact le_add_of_nonneg_left this

            have h31 : 1 / 2 * (b - c)^2 + b * c ≥ b * c := by
                have : 1 / 2 * (b - c)^2 ≥ 0 := by
                    apply mul_nonneg
                    . norm_num
                    . apply pow_two_nonneg
                exact le_add_of_nonneg_left this

            have h32 : 1 / 2 * (c - d)^2 + c * d ≥ c * d := by
                have : 1 / 2 * (c - d)^2 ≥ 0 := by
                    apply mul_nonneg
                    . norm_num
                    . apply pow_two_nonneg
                exact le_add_of_nonneg_left this

            have h33 : 1 / 2 * (d - a)^2 + d * a ≥ d * a := by
                have : 1 / 2 * (d - a)^2 ≥ 0 := by
                    apply mul_nonneg
                    . norm_num
                    . apply pow_two_nonneg
                exact le_add_of_nonneg_left this


            have h3_1 : 1 / 2 * (a - b)^2 + 1/2 * (b - c)^2 + 1/2 * (c - d)^2 + 1 / 2 * (d - a)^2 + a * b + b * c + c * d + d * a ≥ a * b + b * c + c * d + d * a := by
                --Grouping...
                have : 1 / 2 * (a - b)^2 + 1 / 2 * (b - c)^2 + 1 / 2 * (c - d)^2 + 1 / 2 * (d - a)^2 + a * b + b * c + c * d + d * a =
                      (1 / 2 * (a - b)^2 + a * b) + (1 / 2 * (b - c)^2 + b * c) + (1 / 2 * (c - d)^2 + c * d) + (1 / 2 * (d - a)^2 + d * a) := by ring
                rw [this]

                refine add_le_add_three ?_ h32 h33
                exact add_le_add h30 h31

            have h3_2 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ a * b + b * c + c * d + d * a := by
                exact le_of_le_of_eq h3_1 (id (Eq.symm h3))

            rw [←h]
            exact h3_2
            --Second part is done.

        exact ⟨h_part1, h_part2⟩