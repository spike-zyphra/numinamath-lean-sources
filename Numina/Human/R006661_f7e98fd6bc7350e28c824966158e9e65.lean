import Mathlib

/- Finset Icc 1 k = Finset Icc 1 k' disjoint union Finset Icc k'+1 k,
-- given k ≥ k'+1 > 1  -/
lemma l_finset_Icc_disjoint_union {k: ℕ} (k': ℕ) (hk: k ≥ k'+1):
  Finset.Icc 1 k = Finset.Icc 1 k' ∪ Finset.Icc (k'+1) k ∧
  Disjoint (Finset.Icc 1 k') (Finset.Icc (k'+1) k) := by
  constructor
  · have h1: Finset.Icc 1 k' = Finset.Ico 1 (k'+1) := rfl
    have h2: Finset.Icc 1 k = Finset.Ico 1 (k+1) := rfl
    have h3: Finset.Icc (k'+1) k = Finset.Ico (k'+1) (k+1) := rfl
    simp only [h1, h2, h3,
    Nat.succ_eq_succ, Nat.succ_eq_add_one]
    rw [Finset.Ico_union_Ico_eq_Ico]
    <;> simp [hk, Nat.le_of_succ_le]
  · rw [Finset.disjoint_iff_ne]
    intro i1 hi1 i2 hi2
    simp only [Finset.mem_Icc] at hi1 hi2
    omega


/- Let $N$ be a positive integer. Let $P_k = \left( \prod_{i \in \mathbb{N}, 1 \le i \le k} (\lfloor i/7 \rfloor + 1) \right)$.
If $N=50$, show that the largest positive integer $k$ not exceeding $N$ such that $P_k \pmod{13}$ leaves a remainder of $7$ is $49$. -/
theorem number_theory_639794 {P : ℕ → ℕ}
    (hP : ∀ k, P k = ∏ i ∈ Finset.Icc 1 k, (Nat.floor (i / 7 : ℝ) + 1)) :
    IsGreatest {k | 0 < k ∧ k ≤ 50 ∧ P k % 13 = 7} 49 := by

  -- list these values.
  -- for 1 ≤ k ≤ 6, P k is 1, since floor (i/7) = 0
  have case_1_to_6 (k:ℕ) (kge: 1 ≤ k) (kle: k ≤ 6):
    P k = 1 := by
    rw [hP k]
    have: ∀ i ∈ Finset.Icc 1 k, (Nat.floor (i / 7 : ℝ) + 1) = 1 := by
      intro i hi
      simp only [Nat.add_eq_right, Nat.floor_eq_zero]
      cancel_denoms
      simp only [Finset.mem_Icc] at hi
      omega
    simp [Finset.prod_congr rfl this]
  have case1: ∏ i ∈ Finset.Icc (1:ℕ) 6, (Nat.floor (i / 7 : ℝ) + 1) = 1 := by
    rw [← hP, case_1_to_6 6]
    <;> norm_num

  -- if 7j ≤ i ≤ 7j+6, then floor (i/7) = j, and we can compute its product.
  have h_prod {k:ℕ} (j:ℕ) (kge: k ≥ 7 * j) (kle: k ≤ 7*j + 6):
    ∏ i ∈ Finset.Icc (7*j) k, (Nat.floor (i / 7 : ℝ) + 1) =
    ∏ i ∈ Finset.Icc (7*j) k, (j+1) := by
    apply Finset.prod_congr rfl ?_
    intro i hi
    simp only [Finset.mem_Icc] at hi
    simp only [Nat.reduceEqDiff]
    rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> cancel_denoms <;> norm_cast
    · exact hi.left
    · apply lt_of_le_of_lt hi.right ?_
      rw [mul_add_one]
      exact Nat.lt_add_one_of_le kle

  -- for k is 7 to 13, floor (i/7) is 1.
  have case_7_to_13 (k:ℕ) (kge: k ≥ 7) (kle: k ≤ 13):
    P k = ∏ i ∈ Finset.Icc 7 k, 2 := by
    rw [hP k]
    have := l_finset_Icc_disjoint_union 6 kge
    rw [this.left, Finset.prod_union this.right, case1, one_mul]
    rw [h_prod 1]
    <;> simp [kge, kle]
  have case2: ∏ i ∈ Finset.Icc (1:ℕ) 13, (Nat.floor (i / 7 : ℝ) + 1) =
    2^7 := by
    rw [← hP, case_7_to_13]
    <;> norm_num

  -- k from 14 to 20, floor i/7 is 2
  have case_14_to_20 (k:ℕ) (kge: k ≥ 14) (kle: k ≤ 20):
    P k = 2^7 * ∏ i ∈ Finset.Icc 14 k, 3 := by
    rw [hP k]
    obtain ⟨h1, h2⟩ := l_finset_Icc_disjoint_union 13 kge
    rw [h1, Finset.prod_union h2, case2]
    rw [h_prod 2]
    <;> simp [kge, kle]
  have case3: ∏ i ∈ Finset.Icc (1:ℕ) 20, (Nat.floor (i / 7 : ℝ) + 1) =
    2^7 * 3^7 := by
    rw [← hP, case_14_to_20]
    <;> norm_num

  -- k from 21 to 27, floor i/7 is 3
  have case_21_to_27 (k:ℕ) (kge: k ≥ 21) (kle: k ≤ 27):
    P k = 2^7 * 3^7 * ∏ i ∈ Finset.Icc 21 k, 4 := by
    rw [hP k]
    obtain ⟨h1, h2⟩ := l_finset_Icc_disjoint_union 20 kge
    rw [h1, Finset.prod_union h2, case3]
    rw [h_prod 3]
    <;> simp [kge, kle]
  have case4: ∏ i ∈ Finset.Icc (1:ℕ) 27, (Nat.floor (i / 7 : ℝ) + 1) =
    2^7 * 3^7 * 4^7 := by
    rw [← hP, case_21_to_27]
    all_goals simp

  -- k from 28 to 34, floor i/7 is 4
  have case_28_to_34 (k:ℕ) (kge: k ≥ 28) (kle: k ≤ 34):
    P k = 2^7 * 3^7 * 4^7 * ∏ i ∈ Finset.Icc 28 k, 5 := by
    rw [hP k]
    obtain ⟨h1, h2⟩ := l_finset_Icc_disjoint_union 27 kge
    rw [h1, Finset.prod_union h2, case4]
    rw [h_prod 4]
    <;> simp [kge, kle]
  have case5: ∏ i ∈ Finset.Icc (1:ℕ) 34, (Nat.floor (i / 7 : ℝ) + 1) =
    2^7 * 3^7 * 4^7 * 5^7 := by
    rw [← hP, case_28_to_34]
    all_goals simp

  -- similar calculations
  have case_35_to_41 (k:ℕ) (kge: k ≥ 35) (kle: k ≤ 41):
    P k = 2^7 * 3^7 * 4^7 * 5^7 * ∏ i ∈ Finset.Icc 35 k, 6 := by
    rw [hP k]
    obtain ⟨h1, h2⟩ := l_finset_Icc_disjoint_union 34 kge
    rw [h1, Finset.prod_union h2, case5]
    rw [h_prod 5]
    <;> simp [kge, kle]
  have case6: ∏ i ∈ Finset.Icc (1:ℕ) 41, (Nat.floor (i / 7 : ℝ) + 1) =
    2^7 * 3^7 * 4^7 * 5^7 * 6^7 := by
    rw [← hP, case_35_to_41]
    all_goals simp
  have case_42_to_48 (k:ℕ) (kge: k ≥ 42) (kle: k ≤ 48):
    P k = 2^7 * 3^7 * 4^7 * 5^7 * 6^7 * ∏ i ∈ Finset.Icc 42 k, 7 := by
    rw [hP k]
    obtain ⟨h1, h2⟩ := l_finset_Icc_disjoint_union 41 kge
    rw [h1, Finset.prod_union h2, case6]
    rw [h_prod 6]
    <;> simp [kge, kle]
  have case7: ∏ i ∈ Finset.Icc (1:ℕ) 48, (Nat.floor (i / 7 : ℝ) + 1) =
    2^7 * 3^7 * 4^7 * 5^7 * 6^7 * 7^7 := by
    rw [← hP, case_42_to_48]
    all_goals simp
  have case_49_to (k:ℕ) (kge: k ≥ 49) (kle: k ≤ 55):
    P k = (2^7 * 3^7 * 4^7 * 5^7 * 6^7 * 7^7) *
      ∏ i ∈ Finset.Icc 49 k, 8 := by
    rw [hP k]
    obtain ⟨h1, h2⟩ := l_finset_Icc_disjoint_union 48 kge
    rw [h1, Finset.prod_union h2, case7]
    rw [h_prod 7]
    <;> simp [kge, kle]

  -- then P49, P50 is determined.
  have h49 := case_49_to 49 (by norm_num) (by norm_num)
  simp only [Finset.Icc_self, Finset.prod_const,
  Finset.card_singleton, pow_one] at h49
  have h50 := case_49_to 50 (by norm_num) (by norm_num)
  simp only [Finset.prod_const, Nat.card_Icc, Nat.reduceAdd,
  Nat.reduceSub] at h50

  -- calculate 2x3x4x5x6x7 mod 13
  have: (2^7 * 3^7 * 4^7 * 5^7 * 6^7 * 7^7) % 13 = 9 := by
    have: 2*3*4*5*6*7 % 13 = 9 := by norm_num
    simp only [← mul_pow]
    rw [Nat.pow_mod, this]

  -- so P 49 mod 13 is 7, and P 50 not.
  replace h49: P 49 % 13 = 7 := by
    rw [h49, ← Nat.mod_mul_mod, this]
  replace h50: P 50 % 13 ≠ 7 := by
    rw [h50, ← Nat.mod_mul_mod, this]
    norm_num

  -- therefore we claim 49 is the largest one.
  rw [IsGreatest, upperBounds]
  simp only [Set.mem_setOf_eq, Nat.ofNat_pos,
  Nat.reduceLeDiff, true_and, and_imp]

  constructor
  · exact h49
  · intro n npos nle hmod
    suffices n ≠ 50 by omega
    rintro rfl
    apply h50 hmod
