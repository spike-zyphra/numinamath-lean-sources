import Mathlib

/- Let $S_i$ be the set of all integers $n$ such that $100i \leq n < 100(i + 1)$.
For example, $S_4$ is the set $400, 401, 402, \ldots, 499$. How many of the sets
$S_0, S_1, S_2, \ldots, S_{999}$ do not contain a perfect square? -/
theorem number_theory_93827 (S : ℕ → Set ℕ) (hS : ∀ i, S i = {n | 100 * i ≤ n ∧ n < 100 * (i + 1)}) :
    {n | n < 1000 ∧ ¬∃ m, m ^ 2 ∈ S n}.ncard = 708 := by

  -- First, we note that m ^ 2 ∈ S n if and only f(m) = m ^ 2 / 100 = n, using integer division, and that
  -- n <= 999 if and only if m < 317.
  let f : ℕ → ℕ := fun m => m ^ 2 / 100

  have div_100_eq_iff {x n} : x / 100 = n ↔ 100 * n ≤ x ∧ x < 100 * (n + 1) := by
    rw [Nat.eq_iff_le_and_ge, ← Nat.lt_succ_iff, and_comm, Nat.mul_comm 100 n, Nat.mul_comm 100 (n + 1),
      Nat.le_div_iff_mul_le (by norm_num), Nat.div_lt_iff_lt_mul (by norm_num)]

  have sq_mem_S_iff {m n} : m ^ 2 ∈ S n ↔ f m = n := by
    simp [hS, f]
    rw [div_100_eq_iff]

  have f_max_1 {m} : f m < 1000 ↔ m < 317 := by
    simp [f]
    rw [Nat.div_lt_iff_lt_mul (by norm_num), Nat.lt_succ_iff, Nat.lt_succ_iff, ← Nat.le_sqrt']
    norm_num

  -- Thus, the number of sets that do contain a perfect square is the cardinality of the image of f on [0, 317),
  -- and we can get our final answer by subtracting this from 1000.
  have h_eq_f_image : ↑(Finset.Ico 0 1000) ∩ {n | ∃ m, m ^ 2 ∈ S n} = f '' Finset.Ico 0 317 := by
    ext n
    simp
    simp_rw [sq_mem_S_iff]
    constructor
    . rintro ⟨hn, m, hf⟩
      rw [← hf, f_max_1] at hn
      exact ⟨m, hn, hf⟩
    . rintro ⟨m, hm, hf⟩
      rw [← f_max_1, hf] at hm
      exact ⟨hm, ⟨m, hf⟩⟩

  have h_card : (f '' Finset.Ico 0 317).ncard + {n | n < 1000 ∧ ¬∃ m, m ^ 2 ∈ S n}.ncard = 1000 := by
    rw [show {n | n < 1000 ∧ ¬∃ m, m ^ 2 ∈ S n} = ↑(Finset.Ico 0 1000) \ {n | ∃ m, m ^ 2 ∈ S n} by ext n; simp]
    rw [← h_eq_f_image, Set.ncard_inter_add_ncard_diff_eq_ncard _ _, Set.ncard_coe_Finset]
    simp

  -- Next, note that the difference between consecutive squares is more than 100 for m ≥ 50, and less than 100 for m < 50.
  -- This means that if m ≥ 50 then two consecutive squares must fall into different sets (i.e. f is injective on this range),
  -- while if m < 50 then every set contains at least one square.
  have prop_lt_50 {m} (hm : m < 50) : m ^ 2 + 100 ≥ (m + 1) ^ 2 := by linarith
  have prop_ge_50 {m} (hm : m ≥ 50) : m ^ 2 + 100 ≤ (m + 1) ^ 2 := by linarith

  -- Thus we can split our range into [0, 50) and [50, 317), and compute the image cardinality separately.
  have f_max_2 {m} : f m < 25 ↔ m < 50 := by
    simp [f]
    rw [Nat.div_lt_iff_lt_mul (by norm_num), Nat.lt_succ_iff, Nat.lt_succ_iff, ← Nat.le_sqrt']
    norm_num

  -- We check that the images of f are disjoint on the two ranges.
  have : Disjoint (f '' Finset.Ico 0 50) (f '' Finset.Ico 50 317) := by
    refine Set.disjoint_image_image ?_
    simp
    intro m1 hm1 m2 hm2 _
    have : f m1 < 25 := by
      rw [f_max_2]
      exact hm1
    have : f m2 ≥ 25 := by
      contrapose hm2
      simp
      simp at hm2;
      rw [f_max_2] at hm2;
      exact hm2
    linarith

  -- Now we show that on [0, 50), f is surjective onto [0, 25). For each n, we let
  -- m = sqrt(100 * (n + 1) - 1), using the integer square root function defined by
  -- sqrt x = m iff m ^ 2 <= x < (m + 1) ^ 2.
  have hf_image_low : f '' Finset.Ico 0 50 = Finset.Ico 0 25 := by
    ext n
    simp
    constructor
    . intro ⟨m, ⟨hm, hmn⟩⟩
      rw [← hmn, f_max_2]
      exact hm
    . intro hn
      let m := Nat.sqrt (100 * (n + 1) - 1)
      have hm : m < 50 := by
        simp [m]
        rw [Nat.sqrt_lt]
        refine Nat.sub_one_lt_of_le (by simp) ?_
        linarith
      have hmn : f m = n := by
        simp [f]
        rw [div_100_eq_iff]
        and_intros
        . refine @Nat.le_of_add_le_add_right _ 100 _ ?_
          refine Nat.le_trans ?_ (prop_lt_50 hm)
          refine Nat.le_of_pred_lt ?_
          rw [show Nat.pred (100 * n + 100) = 100 * (n + 1) - 1 by ring_nf; simp]
          simp [m]
          exact Nat.lt_succ_sqrt' _
        . simp [m]
          refine Nat.lt_of_le_of_lt (Nat.sqrt_le' _) ?_
          simp
      exact ⟨m, ⟨hm, hmn⟩⟩

  -- We can show that f is injective on [50, 317) by showing that it is strictly increasing.
  have hf_image_high : Set.InjOn f (Finset.Ico 50 317) := by
    have f_mono : Monotone f := by
      intro m1 m2 h
      simp [f]
      refine Nat.div_le_div_right ?_
      rw [pow_two, pow_two]
      exact Nat.mul_self_le_mul_self h
    refine StrictMonoOn.injOn ?_
    simp [StrictMonoOn]
    rintro m1 hm1l hm1r m2 hm2l hm2r h
    rw [← Nat.succ_lt_succ_iff, Nat.lt_succ_iff] at h
    refine Nat.lt_of_lt_of_le ?_ (f_mono h)
    simp [f]
    rw [← Nat.succ_lt_succ_iff, Nat.lt_succ_iff]
    rw [show Nat.succ (m1 ^ 2 / 100) = m1 ^ 2 / 100 + 100 / 100 by simp]
    refine Nat.le_trans (Nat.add_div_le_add_div _ _ _) ?_
    refine Nat.div_le_div_right ?_
    exact prop_ge_50 hm1l

  -- Thus we can compute the image cardinality on [0, 317) by adding the two halves.
  have : (f '' Finset.Ico 0 317).ncard = 292 := by
    rw [← Finset.Ico_union_Ico_eq_Ico (show 0 ≤ 50 by norm_num) (show 50 ≤ 317 by norm_num),
      Finset.coe_union, Set.image_union, Set.ncard_union_eq this, hf_image_low,
      Set.ncard_image_of_injOn hf_image_high, Set.ncard_coe_Finset, Set.ncard_coe_Finset]
    simp

  -- Finally, we can compute the answer by subtracting this from 1000.
  have : 292 + {n | n < 1000 ∧ ¬∃ m, m ^ 2 ∈ S n}.ncard = 1000 := by rw [← this, h_card]
  linarith