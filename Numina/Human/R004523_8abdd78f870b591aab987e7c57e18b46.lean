import Mathlib


/- Example 3 Solve the inequalities:
(1) $\frac{1}{x-1} \leqslant x-1$;
(2) $\frac{1}{4-x}+\frac{2}{2+x} \leqslant 1$. -/
theorem inequalities_278942 {x : ℝ} :
  (x ≠ 1 → (1 / (x - 1) ≤ x - 1 ↔ x ∈ Set.Ico 0 1 ∪ Set.Ici 2)) ∧
  (x ≠ 4 → x ≠ - 2 → ((1 / (4 - x) + 2 / (2 + x) ≤ 1) ↔
    x ∈ Set.Iio (-2 : ℝ) ∪ Set.Icc 1 2 ∪ Set.Ioi 4)) := by

  constructor

  · intro xne1
    -- solve first inequality
    have hx: x-1 ≠ 0 := by
      rintro hx
      absurd xne1
      linarith only [hx]
    rw [← tsub_nonpos, div_sub' _ _ _ hx]
    rw [show 1-(x-1)*(x-1) = x*(2-x) by ring]
    rcases xne1.lt_or_lt with hx | hx
    · rw [← sub_neg] at hx
      simp only [div_nonpos_iff, hx.le, and_true, sub_nonneg,
      Set.mem_union, Set.mem_Ico, Set.mem_Ici]
      have hx1: 0 < 2-x := by linarith only [hx]
      have hx2: x < 2 := by linarith only [hx1]
      simp only [hx1, mul_nonneg_iff_of_pos_right,
      mul_nonpos_iff_neg_imp_nonneg, true_implies, hx1.le, implies_true, true_and]
      constructor
      · rintro (h1 | h1)
        · left
          constructor <;> linarith only [h1, hx]
        · linarith only [h1.left, h1.right]
      · rintro (h1 | h1)
        · left; exact h1.left
        · linarith only [hx2, h1]
    · have hx': 0 < x-1 := by linarith only [hx]
      rw [div_nonpos_iff]
      have hx1: 0 < x := by linarith only [hx]
      simp only [hx1, mul_nonneg_iff_of_pos_left, sub_nonneg,
      tsub_le_iff_right, zero_add, hx'.le,
      and_true, Set.mem_union, Set.mem_Ico, Set.mem_Ici]
      rw [mul_nonpos_iff_pos_imp_nonpos]
      simp only [hx1, tsub_le_iff_right, zero_add, forall_const,
      sub_neg, hx1.le, implies_true, and_true, true_and]
      constructor
      · rintro (h1 | h1)
        · left
          apply lt_of_le_of_ne h1.right xne1
        · right; exact h1
      · rintro (h1 | h1)
        · left
          constructor <;> linarith only [h1]
        · right; exact h1


  · intro hx1 hx2
    have hx1': 4-x ≠ 0 := by
      rintro h
      absurd hx1
      linarith only [h]
    have hx2': 2+x ≠ 0 := by
      rintro h
      absurd hx2
      linarith only [h]
    -- solve second inequality
    rw [div_add_div _ _ hx1' hx2', one_mul,
    ← tsub_nonpos, div_sub_one (by simp [hx1', hx2'])]
    have: 2+x + (4-x)*2 - (4-x)*(2+x) =
      (x-1) * (x-2) := by ring
    rw [this]
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Ioi]
    rcases hx1.lt_or_lt with hx1 | hx1
    · have h1: ¬ 4 < x := by simp [hx1.le]
      have h2: 0 < 4 - x := by linarith only [hx1]
      rcases hx2.lt_or_lt with hx2 | hx2
      · have h3: 2+x < 0 := by linarith only [hx2]
        have h4: x-1 < 0 := by linarith only [hx2]
        have h5: x-2 < 0 := by linarith only [hx2]
        simp only [div_nonpos_iff, h4.le, h5.le,
        mul_nonneg_of_nonpos_of_nonpos, h2.le, h3.le,
        mul_nonpos_of_nonneg_of_nonpos,
        and_self, true_or, hx2, h1, or_false]
      · have h3: ¬ x < -2 := by simp [hx2.le]
        simp only [h3, false_or, h1, or_false]
        have h4: 0 < 2+x := by linarith only [hx2]
        have h5: 0 < (4-x)*(2+x) := mul_pos h2 h4
        have h6: ¬ (4-x) * (2+x) ≤ 0 := by simp [h5]
        simp only [div_nonpos_iff, h6, and_false, h5.le, and_true, false_or]
        constructor
        · intro hh
          rw [mul_nonpos_iff] at hh
          rcases hh with hh | hh
          · constructor <;> linarith only [hh]
          · linarith only [hh]
        · intro hh
          apply mul_nonpos_of_nonneg_of_nonpos
          <;> linarith only [hh]
    · simp only [hx1, or_true, iff_true, ge_iff_le]
      have h1: 0 < (x-1)*(x-2) := by
        apply mul_pos
        <;> linarith only [hx1]
      have h2: (4-x)*(2+x) < 0 := by
        apply mul_neg_of_neg_of_pos
        <;> linarith only [hx1]
      apply div_nonpos_of_nonneg_of_nonpos h1.le h2.le