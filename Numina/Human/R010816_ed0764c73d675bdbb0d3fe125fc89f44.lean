import Mathlib

/- Let x1 ≤ x2 ≤ ⋯ ≤ x100  be real numbers such that ∣x1∣ + ∣x2∣ + ⋯ + ∣x100∣ = 1 and x1 + x2 + ⋯ + x100 = 0.
Among all such 100-tuples of numbers, the greatest value that x76 − x16​ can achieve is m / n​, where m and n are relatively prime positive integers.
Find m + n. -/
theorem algebra_98636 :
    IsGreatest {d | ∃ x : Fin 100 → ℝ, d = x 75 - x 15 ∧ (∀ i j, i ≤ j → x i ≤ x j) ∧ ∑ i, |x i| = 1 ∧ ∑ i, x i = 0} (41 / 800) := by
  simp only [IsGreatest, Fin.isValue, Set.mem_setOf_eq, upperBounds, forall_exists_index, and_imp]
  have hnorm : (15 : Fin 100) = (15 : ℝ) ∧ (75 : Fin 100) = (75 : ℝ) := ⟨rfl, rfl⟩
  -- we need to prove that there exists a sequence f with all required properties
  -- such that f 75 - f 16 = 41 / 800 and that for any sequence x with all required properties
  -- the inequality x 75 - x 16 ≤ 41 / 800 holds
  constructor
  · set f : Fin 100 → ℝ := fun i => if i ≤ 15 then -1 / 32 else if 75 ≤ i then 1 / 50 else 0 with f_eq
    -- Define f as follows: f i = -1 / 32 when i ≤ 15, f i = 1 / 50 when 75 ≤ i,  and f i = 0 for other i.
    -- Prove that f satisfies all requirements and f 75 - f 16 = 41 / 800.
    have hfabs i : |f i| = if i ≤ 15 then 1 / 32 else if 75 ≤ i then 1 / 50 else 0 := by
      simp [f]; split_ifs <;> norm_num
    have h15_le : Finset.filter (fun x : Fin 100 ↦ x ≤ 15) Finset.univ = Finset.Iic 15 := rfl
    have h15_gt : Finset.filter (fun x : Fin 100 ↦ 15 < x) Finset.univ = Finset.Ici 16 := rfl
    have h75_le : Finset.filter (fun x : Fin 100 ↦ 75 ≤ x) (Finset.Ici 16) = Finset.Ici 75 := by rfl
    use f
    refine ⟨by simp [f]; norm_num, ?_, ?_, ?_⟩
    -- it is easy to show that f i ≤ f j for all i ≤ j
    · intro i j hij
      simp [f]; split_ifs <;> norm_num <;> omega
    -- we have ∑ i, |f i| = ∑ i, if i ≤ 15 then 1 / 32 else if 75 ≤ i then 1 / 50 else 0
    --                    = ∑ i ∈ [0, 15], 1 / 32 + ∑ i ∈ [75, 99], 1 / 50
    --                    = 16 * 1 / 32 + 25 * 1 / 50 = 1
    · calc ∑ i : Fin 100, |f i|
           = ∑ i : Fin 100, if i ≤ 15 then 1 / 32 else if 75 ≤ i then 1 / 50 else 0 := by
            congr; simp [hfabs]
         _ = 1 := by
            simp [Finset.sum_ite, h15_le, h15_gt, h75_le, hnorm]
            norm_num
    -- we have ∑ i, f i = ∑ i ∈ [0, 15], -1 / 32 + ∑ i ∈ [75, 99], 1 / 50
    --                  = 16 * -1 / 32 + 25 * 1 / 50 = 0
    · simp [f, Finset.sum_ite, h15_le, h15_gt, h75_le, hnorm]
      norm_num
  -- show that if x satisfies all requirements then x 75 - x 15 ≤ 41 / 800
  · intro s x hseq hmono hsum_abs hsum
    -- it is enough to show that x 75 ≤ 1 / 50 and -1 / 32 ≤ x 15
    suffices x 75 ≤ 1 / 50 ∧ -1 / 32 ≤ x 15 by linarith
    constructor
    · contrapose! hsum_abs
      -- assume that x 75 > 1 / 50 and show that ∑ i, |x i| > 1 in this case
      apply ne_of_gt
      set s1 := Finset.Iio (75 : Fin 100)
      set s2 := Finset.Ici (75 : Fin 100)
      have hs12 : Disjoint s1 s2 := Finset.disjoint_iff_inter_eq_empty.mpr rfl
      have hs12univ : s1 ∪ s2 = Finset.univ := by ext i; simp [s1, s2]; exact Fin.lt_or_le i 75
      calc
        ∑ i, |x i| = ∑ i ∈ s1, |x i| + ∑ i ∈ s2, |x i| := by rw [←hs12univ, Finset.sum_union hs12]
        _ ≥ ∑ i ∈ s1, |x i| + 25 * x 75 := by
              gcongr
              simp [s2]
              apply le_trans _ (Finset.card_nsmul_le_sum _ _ (x 75) _)
              · simp [hnorm]; norm_num
              simp; intro i hi
              apply le_trans _ (le_abs_self _)
              exact hmono _ _ hi
        _ > |∑ i ∈ s1, x i| + 1 / 2 := by
              apply add_lt_add_of_le_of_lt _ (by linarith)
              exact Finset.abs_sum_le_sum_abs x s1
        _ = |∑ i ∈ s2, x i| + 1 / 2 := by
              rw [←abs_neg]
              congr
              rw [←hs12univ, Finset.sum_union hs12] at hsum
              linarith
        _ ≥ 25 * x 75 + 1 / 2 := by
              gcongr
              rw [Finset.abs_sum_of_nonneg]
              · apply le_trans _ (Finset.card_nsmul_le_sum _ _ (x 75) _)
                · simp [s2, hnorm]; norm_num
                · simp [s2]; intro i hi; exact hmono _ _ hi
              simp [s2]; intro i hi
              linarith [hmono _ _ hi]
        _ > 1 := by linarith
    · contrapose! hsum_abs
      -- assume that x 15 < -1 / 32 and show that ∑ i, |x i| > 1 in this case
      apply ne_of_gt
      set s1 := Finset.Iic (15 : Fin 100)
      set s2 := Finset.Ioi (15 : Fin 100)
      have h15 : 1 / 32 < |x 15| := by rw [lt_abs]; right; linarith
      have hs12 : Disjoint s1 s2 := Finset.disjoint_iff_inter_eq_empty.mpr rfl
      have hs12univ : s1 ∪ s2 = Finset.univ := by ext i; simp [s1, s2]; exact Fin.le_or_lt i _
      calc
        ∑ i, |x i| = ∑ i ∈ s1, |x i| + ∑ i ∈ s2, |x i| := by rw [←hs12univ, Finset.sum_union hs12]
        _ ≥ 16 * |x 15| + ∑ i ∈ s2, |x i| := by
              gcongr
              simp [s1]
              apply le_trans _ (Finset.card_nsmul_le_sum _ _ |x 15| _)
              · simp [hnorm]; norm_num
              simp; intro i hi
              apply abs_le_abs_of_nonpos (by linarith)
              exact hmono _ _ hi
        _ > 1 / 2 + |∑ i ∈ s2, x i| := by
              apply add_lt_add_of_lt_of_le (by linarith)
              exact Finset.abs_sum_le_sum_abs x s2
        _ = 1 / 2 + |∑ i ∈ s1, x i| := by
              rw [←abs_neg]
              congr
              rw [←hs12univ, Finset.sum_union hs12] at hsum
              linarith
        _ ≥ 1 / 2 + 16 * |x 15| := by
              gcongr
              nth_rw 2 [← abs_neg]
              rw [← neg_one_mul, Finset.mul_sum, Finset.abs_sum_of_nonneg]
              · apply le_trans _ (Finset.card_nsmul_le_sum _ _ |x 15| _)
                · simp [s1, hnorm]; norm_num
                · simp [s1]; intro i hi
                  suffices x i ≤ 0 by
                    rw [←abs_of_nonpos this]; apply abs_le_abs_of_nonpos (by linarith)
                    exact hmono _ _ hi
                  exact le_trans (hmono _ _ hi) (by linarith)
              simp [s1]; intro i hi
              linarith [hmono _ _ hi]
        _ > 1 := by linarith