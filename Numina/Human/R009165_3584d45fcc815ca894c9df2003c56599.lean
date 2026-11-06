import Mathlib

/-Let $f(n)$ be the integer closest to $\sqrt[4]{n}.$ Find $\sum_{k=1}^{1995}\frac 1{f(k)}.$-/
theorem algebra_12508 : ∑ i ∈ Finset.Icc (1:ℕ) 1995, (1:ℝ) / round ((i:ℝ) ^ ((1:ℝ)/4)) = 400 := by
-- Split the numbers from $1$ to $1995$ to the following union of subsets
  have aux: Finset.Icc 1 1995 = Finset.Icc 1 5 ∪ Finset.Icc 6 39 ∪ Finset.Icc 40 150 ∪
  Finset.Icc 151 410 ∪ Finset.Icc 411 915 ∪ Finset.Icc 916 1785 ∪ Finset.Icc 1786 1995 := by
    ext i; simp; constructor
    · contrapose!; rintro ⟨h1,⟨h2,⟨h3,⟨h4,⟨h5,⟨h6,h7⟩⟩⟩⟩⟩⟩ h8
      exact h7 (h6 (h5 (h4 (h3 (h2 (h1 h8))))))
    contrapose!; intro h; split_ands
    all_goals intro h'; replace h := h (show _ by linarith); linarith
-- Prove that for numbers in the first set, $1$ divides the round function equals $1$
  have rdeq1 : ∀ i, i ∈ Finset.Icc (1:ℕ) 5 → (1:ℝ) / round ((i:ℝ) ^ ((1:ℝ)/4)) = 1 := by
    intro i hi; simp at hi; simp [round_eq, Int.floor_eq_iff]
    rify at hi; constructor
    · have : (1:ℝ) ≤ i ^ (4⁻¹:ℝ) := by apply Real.one_le_rpow; linarith; norm_num
      apply le_add_of_le_of_nonneg; assumption; norm_num
    rw [← lt_sub_iff_add_lt]; norm_num;
    rw [← Real.rpow_lt_rpow_iff _ _ (show 0<(4:ℝ) by norm_num)]
    rw [← Real.rpow_mul]; norm_num; linarith
    any_goals linarith
    apply Real.rpow_nonneg; linarith
-- Prove that for numbers in the second set, $1$ divides the round function equals $1/2$
  have rdeq2 : ∀ i, i ∈ Finset.Icc (6:ℕ) 39 → (1:ℝ) / round ((i:ℝ) ^ ((1:ℝ)/4)) = 1/2 := by
    intro i hi; simp at hi; simp [round_eq]; nth_rw 2 [← show (2:ℤ)=(2:ℝ) by rfl]
    rw [Int.cast_inj, Int.floor_eq_iff]
    rify at hi; constructor
    · rw [← sub_le_iff_le_add, ← Real.rpow_le_rpow_iff _ _ (show 0<(4:ℝ) by norm_num)]
      rw [← Real.rpow_mul]; norm_num; any_goals linarith
      norm_num; apply Real.rpow_nonneg; linarith
    rw [← lt_sub_iff_add_lt]; norm_num;
    rw [← Real.rpow_lt_rpow_iff _ _ (show 0<(4:ℝ) by norm_num)]
    rw [← Real.rpow_mul]; norm_num; linarith
    any_goals linarith
    apply Real.rpow_nonneg; linarith
-- Prove that for numbers in the third set, $1$ divides the round function equals $1/3$
  have rdeq3 : ∀ i, i ∈ Finset.Icc (40:ℕ) 150 → (1:ℝ) / round ((i:ℝ) ^ ((1:ℝ)/4)) = 1/3 := by
    intro i hi; simp at hi; simp [round_eq]; rw [← show (3:ℤ)=(3:ℝ) by rfl]
    rw [Int.cast_inj, Int.floor_eq_iff]
    rify at hi; constructor
    · rw [← sub_le_iff_le_add, ← Real.rpow_le_rpow_iff _ _ (show 0<(4:ℝ) by norm_num)]
      rw [← Real.rpow_mul]; norm_num; any_goals linarith
      norm_num; apply Real.rpow_nonneg; linarith
    rw [← lt_sub_iff_add_lt]; norm_num;
    rw [← Real.rpow_lt_rpow_iff _ _ (show 0<(4:ℝ) by norm_num)]
    rw [← Real.rpow_mul]; norm_num; linarith
    any_goals linarith
    apply Real.rpow_nonneg; linarith
-- Prove that for numbers in the 4th set, $1$ divides the round function equals $1/4$
  have rdeq4 : ∀ i, i ∈ Finset.Icc (151:ℕ) 410 → (1:ℝ) / round ((i:ℝ) ^ ((1:ℝ)/4)) = 1/4 := by
    intro i hi; simp at hi; simp [round_eq]; rw [← show (4:ℤ)=(4:ℝ) by rfl]
    rw [Int.cast_inj, Int.floor_eq_iff]
    rify at hi; constructor
    · rw [← sub_le_iff_le_add, ← Real.rpow_le_rpow_iff _ _ (show 0<(4:ℝ) by norm_num)]
      rw [← Real.rpow_mul]; norm_num; any_goals linarith
      norm_num; apply Real.rpow_nonneg; linarith
    rw [← lt_sub_iff_add_lt]; norm_num;
    rw [← Real.rpow_lt_rpow_iff _ _ (show 0<(4:ℝ) by norm_num)]
    rw [← Real.rpow_mul]; norm_num; linarith
    any_goals linarith
    apply Real.rpow_nonneg; linarith
-- Prove that for numbers in the 5th set, $1$ divides the round function equals $1/5$
  have rdeq5 : ∀ i, i ∈ Finset.Icc (411:ℕ) 915 → (1:ℝ) / round ((i:ℝ) ^ ((1:ℝ)/4)) = 1/5 := by
    intro i hi; simp at hi; simp [round_eq]; rw [← show (5:ℤ)=(5:ℝ) by rfl]
    rw [Int.cast_inj, Int.floor_eq_iff]
    rify at hi; constructor
    · rw [← sub_le_iff_le_add, ← Real.rpow_le_rpow_iff _ _ (show 0<(4:ℝ) by norm_num)]
      rw [← Real.rpow_mul]; norm_num; any_goals linarith
      norm_num; apply Real.rpow_nonneg; linarith
    rw [← lt_sub_iff_add_lt]; norm_num;
    rw [← Real.rpow_lt_rpow_iff _ _ (show 0<(4:ℝ) by norm_num)]
    rw [← Real.rpow_mul]; norm_num; linarith
    any_goals linarith
    apply Real.rpow_nonneg; linarith
-- Prove that for numbers in the 6th set, $1$ divides the round function equals $1/6$
  have rdeq6 : ∀ i, i ∈ Finset.Icc (916:ℕ) 1785 → (1:ℝ) / round ((i:ℝ) ^ ((1:ℝ)/4)) = 1/6 := by
    intro i hi; simp at hi; simp [round_eq]; rw [← show (6:ℤ)=(6:ℝ) by rfl]
    rw [Int.cast_inj, Int.floor_eq_iff]
    rify at hi; constructor
    · rw [← sub_le_iff_le_add, ← Real.rpow_le_rpow_iff _ _ (show 0<(4:ℝ) by norm_num)]
      rw [← Real.rpow_mul]; norm_num; any_goals linarith
      norm_num; apply Real.rpow_nonneg; linarith
    rw [← lt_sub_iff_add_lt]; norm_num;
    rw [← Real.rpow_lt_rpow_iff _ _ (show 0<(4:ℝ) by norm_num)]
    rw [← Real.rpow_mul]; norm_num; linarith
    any_goals linarith
    apply Real.rpow_nonneg; linarith
-- Prove that for numbers in the 7th set, $1$ divides the round function equals $1/7$
  have rdeq7 : ∀ i, i ∈ Finset.Icc (1786:ℕ) 1995 → (1:ℝ) / round ((i:ℝ) ^ ((1:ℝ)/4)) = 1/7 := by
    intro i hi; simp at hi; simp [round_eq]; rw [← show (7:ℤ)=(7:ℝ) by rfl]
    rw [Int.cast_inj, Int.floor_eq_iff]
    rify at hi; constructor
    · rw [← sub_le_iff_le_add, ← Real.rpow_le_rpow_iff _ _ (show 0<(4:ℝ) by norm_num)]
      rw [← Real.rpow_mul]; norm_num; any_goals linarith
      norm_num; apply Real.rpow_nonneg; linarith
    rw [← lt_sub_iff_add_lt]; norm_num;
    rw [← Real.rpow_lt_rpow_iff _ _ (show 0<(4:ℝ) by norm_num)]
    rw [← Real.rpow_mul]; norm_num; linarith
    any_goals linarith
    apply Real.rpow_nonneg; linarith
-- Use the above lemmas, Finset.sum_union and Finset.sum_congr to simplify the final goal
  rw [aux]; repeat rw [Finset.sum_union];
  rw [Finset.sum_congr (show Finset.Icc 1 5=Finset.Icc 1 5 by rfl) rdeq1]
  rw [Finset.sum_congr (show Finset.Icc 6 39=Finset.Icc 6 39 by rfl) rdeq2]
  rw [Finset.sum_congr (show Finset.Icc 40 150=Finset.Icc 40 150 by rfl) rdeq3]
  rw [Finset.sum_congr (show Finset.Icc 151 410=Finset.Icc 151 410 by rfl) rdeq4]
  rw [Finset.sum_congr (show Finset.Icc 411 915=Finset.Icc 411 915 by rfl) rdeq5]
  rw [Finset.sum_congr (show Finset.Icc 916 1785=Finset.Icc 916 1785 by rfl) rdeq6]
  rw [Finset.sum_congr (show Finset.Icc 1786 1995=Finset.Icc 1786 1995 by rfl) rdeq7]
-- Finish the rest trivial disjointness goals by applying disjoint_iff and simplify
  norm_num; all_goals rw [disjoint_iff]; simp; ext i; simp
  · intros; linarith
  all_goals rintro ⟨⟩ _; any_goals linarith
  all_goals rename_i h h'; cases h; any_goals linarith
  all_goals rename_i h; cases h; any_goals linarith
  all_goals rename_i h; cases h; any_goals linarith
  rename_i h; cases h; any_goals linarith