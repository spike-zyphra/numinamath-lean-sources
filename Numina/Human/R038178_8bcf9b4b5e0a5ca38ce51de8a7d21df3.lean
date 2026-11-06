import Mathlib

/- Show that
$$
\frac{1}{2^{2}}+\frac{1}{3^{2}}+\ldots+\frac{1}{n^{2}}<\frac{2}{3}
$$
for all $n \geq 2$. -/
theorem inequalities_607935 (n : ℕ) (hn : 2 ≤ n) :
  ∑ i ∈ Finset.Icc 2 n, (1 / i^2 : ℝ) < 2 / 3 := by
  -- notice that 1/j^2 < 1/(j-1) - 1/j
  have h1(j: ℕ)(hj: 2 ≤ j): (1/j^2: ℝ) < 1/(j-1) - 1/j := by
    rify at hj
    --1/j^2 < 1/(j-1)j
    have: (1/j^2: ℝ) < 1/((j-1)*j) := by
      apply (one_div_lt_one_div ?_ ?_).mpr
      · nlinarith [hj]
      · apply pow_pos (by linarith [hj])
      · apply mul_pos (by linarith [hj]) (by linarith [hj])
    apply lt_of_lt_of_le this (le_of_eq ?_)
    replace this: (j-1:ℝ) ≠ 0 := by
      symm; apply ne_of_lt (by linarith [hj])
    field_simp [this]
  -- therefore sum from k to n < 1/(k-1)
  have h2(k:ℕ)(hk1: k ≤ n)(hk2: 2 ≤ k): ∑ i ∈ Finset.Icc k n, (1/i^2:ℝ) < 1/(k-1) := by
    have hh1: ∑ i ∈ Finset.Icc k n, (1/i^2:ℝ) <
      ∑ i ∈ Finset.Icc k n, (1/(i-1) - 1/i: ℝ) := by
      have: ∀i ∈ Finset.Icc k n, (1/i^2:ℝ) < (1/(i-1) - 1/i) := by
        intro i hi;
        apply h1 i ?_
        simp at hi
        apply le_trans hk2 hi.left
      apply Finset.sum_lt_sum_of_nonempty ?_ this
      apply Finset.nonempty_Icc.mpr hk1
    -- 1/(k-1) - 1/k + 1/k - 1/(k+1) +... + 1/(n-1) - 1/n = 1/(k-1) - 1/n
    have hh2: ∑ i ∈ Finset.Icc k n, (1/(i-1) - 1/i: ℝ) =
      1/(k-1) - 1/n := by
      clear * - hk1
      induction' n,hk1 using Nat.le_induction with n hk1 ih
      · simp
      · have: k ≤ n+1 := by linarith [hk1]
        rw [Finset.sum_Icc_succ_top this, ih]
        push_cast
        ring
    apply lt_of_lt_of_le hh1
    rw [hh2]; simp
  -- so sum from 1/2^2 to 1/n^2 < sum from 1/2^2 to 1/5^2 + 1/5
  have h3: ∑ i ∈ Finset.Icc 2 n, (1/i^2: ℝ) <
    (∑ i ∈ Finset.Icc (2:ℕ) 5, (1/i^2: ℝ)) + 1/5 := by
    by_cases hn': n ≤ 5
    · have: ∑ i ∈ Finset.Icc 2 n, (1/i^2: ℝ) ≤
        ∑ i ∈ Finset.Icc (2:ℕ) 5, (1/i^2: ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Icc_subset_Icc_right hn'
        · intro _ _ _; simp
      linarith [this]
    replace hn': 6 ≤ n := by omega
    -- sum from 2 to n = sum from 2 to 5 + sum from 6 to n
    have: ∑ i ∈ Finset.Icc 2 n, (1/i^2: ℝ) =
      ∑ i ∈ Finset.Icc (2:ℕ) 5, (1/i^2: ℝ) +
      ∑ i ∈ Finset.Icc 6 n, (1/i^2: ℝ) := by
      have hh1: Finset.Icc 2 n = (Finset.Icc 2 5) ∪ (Finset.Icc 6 n) := by
        have: Finset.Icc 2 5 = Finset.Ico 2 6 := rfl
        rw [this]
        refine Finset.coe_inj.mp ?_
        push_cast; symm
        apply Set.Ico_union_Icc_eq_Icc (by norm_num) hn'
      have hh2: Disjoint (Finset.Icc 2 5) (Finset.Icc 6 n) := by
        rw [Finset.disjoint_iff_ne]
        simp
        intro a _ ha b hb _
        omega
      rw [hh1, Finset.sum_union hh2]
    rw [this]
    linarith [h2 6 hn' (by norm_num)]
  apply lt_trans h3 ?_
  -- left side is 1/2^2+1/3^2+1/4^2+1/5^2+1/5 = 2389/3600 < 2/3
  simp [← Finset.sum_Ioc_add_eq_sum_Icc, Finset.sum_Ioc_succ_top]
  norm_num