import Mathlib

/- 6. Let's call the distance between numbers the absolute value of their difference. It is known that the sum of the distances from seven consecutive natural numbers to some number $a$ is 609, and the sum of the distances from these same seven numbers to some number $b$ is 721. Find all possible values of $a$, given that $a+b=192$. -/
theorem algebra_156880 (a b : ℝ) (k : ℕ) (ha : ∑ i ∈ Finset.Icc k (k + 6), |i - a| = 609)
    (hb : ∑ i ∈ Finset.Icc k (k + 6), |i - b| = 721) (h : a + b = 192) :
    a = 104 ∨ a = 191 ∨ a = 1 := by
      -- We sum 7 values
      have s_card : (Finset.Icc k (k + 6)).card = 7 := by
        simp only [Nat.card_Icc]
        omega

      -- If the value is in the range [k, k + 6] then the sum is less than 42
      have sum_in : ∀ x: ℝ, x ∈ Set.Icc (k : ℝ) ((k + 6) : ℝ) → ∑ i ∈ Finset.Icc k (k + 6), |i - x| ≤ 42 := by
        intro x xh
        convert_to ∑ i ∈ Finset.Icc k (k + 6), |↑i - x| ≤ (Finset.Icc k (k + 6)).card • 6
        · norm_num [s_card]
        apply Finset.sum_le_card_nsmul

        -- Each part is less than or equal to 6
        intro k' kh'
        simp only [Finset.mem_Icc] at kh'
        simp only [Set.mem_Icc] at xh
        have ⟨kh1, kh2⟩ := kh'
        have ⟨xh1, xh2⟩ := xh
        cases' abs_cases (k' - x) with h1 h2
        · simp only [h1.1, tsub_le_iff_right, ge_iff_le]
          refine le_trans (Nat.cast_le.mpr kh2) ?_
          simp only [Nat.cast_add, Nat.cast_ofNat]
          linarith
        · simp only [h2.1, neg_sub, tsub_le_iff_right, ge_iff_le]
          refine le_trans xh2 ?_
          rw [add_comm]
          simp only [add_le_add_iff_left, Nat.cast_le]
          exact kh1

      -- so we have that a is outside the range
      have a_values : a < k ∨ k + 6 < a := by
        -- assume that it's inside the range
        by_contra h
        -- but then it's value must be less than we know it is
        simp only [not_or, not_lt] at h
        linarith only [ha ▸ (sum_in a h)]

      -- similarly for b
      have b_values : b < k ∨ k + 6 < b := by
        -- assume that it's inside the range
        by_contra h
        -- but then it's value must be less than we know it is
        simp only [not_or, not_lt] at h
        linarith only [hb ▸ (sum_in b h)]

      -- We can simplify the sum if x is below the range
      have sum_neg : ∀ {x : ℝ}, x < k → ∑ i ∈ Finset.Icc k (k + 6), |i - x| = 7 * k + 7 * 3 - 7 * x := by
        intro x xh
        convert_to ∑ i ∈ Finset.Icc k (k + 6), (i - x) = 7 * ↑k + 7 * 3 - 7 * x
        · apply Finset.sum_congr rfl
          simp only [Finset.mem_Icc, abs_eq_self, sub_nonneg, and_imp]
          intro aa bb cc
          refine le_trans xh.le ?_
          exact Nat.cast_le.mpr bb
        iterate 6 rw [Finset.sum_Icc_succ_top]
        simp only [Finset.Icc_self, Finset.sum_singleton]
        field_simp
        all_goals
        · linarith

      -- We can simplify the sum if x is above the range
      have sum_pos : ∀ {x : ℝ}, k + 6 < x → ∑ i ∈ Finset.Icc k (k + 6), |i - x| = 7 * x - 7 * k - 7 * 3 := by
        intro x xh
        convert_to ∑ i ∈ Finset.Icc k (k + 6), -(i - x) = 7 * x - 7 * k - 7 * 3
        · apply Finset.sum_congr rfl
          simp only [Finset.mem_Icc, and_imp]
          intro nn rr tt
          apply abs_of_neg
          rw [sub_neg]
          refine lt_of_le_of_lt ?_ xh
          convert_to (nn : ℝ) ≤ (((k + 6) : ℕ) : ℝ)
          norm_num
          exact Nat.cast_le.mpr tt
        iterate 6 rw [Finset.sum_Icc_succ_top]
        simp only [Finset.Icc_self, Finset.sum_singleton]
        field_simp
        all_goals
        · linarith

      -- Check cases
      cases' a_values with a1 a2
      · cases' b_values with b1 b2
        -- Both are to the left of the interval, a = 104
        · rw [sum_neg a1] at ha
          rw [sum_neg b1] at hb
          refine Or.inl ?_
          linarith only [ha, hb, h]
        -- a is to the left and b is to the right, a = 1
        · rw [sum_neg a1] at ha
          rw [sum_pos b2] at hb
          refine Or.inr <| Or.inr ?_
          linarith only [ha, hb, h]
      · cases' b_values with b1 b2
        -- a is to the right and b is to the left, a = 191
        · rw [sum_pos a2] at ha
          rw [sum_neg b1] at hb
          refine Or.inr <| Or.inl ?_
          linarith only [ha, hb, h]
        -- Both are to the right of the interval, no valid solutions
        · rw [sum_pos a2] at ha
          rw [sum_pos b2] at hb
          linarith only [ha, hb, h]