import Mathlib

/- For how many positive integers $n$ does $1+2+\cdots+n$ evenly divide $6n$? -/
theorem algebra_13992 : {n : ℕ | n ≠ 0 ∧ (∑ i in Finset.Icc 1 n, i) ∣ 6 * n}.ncard = 5 := by
  have {n : ℕ} (hn : n ≠ 0) :
      (∑ i in Finset.Icc 1 n, i) ∣ 6 * n ↔ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 11 := by
    have g : ∑ i ∈ Finset.Icc 1 n, i = ∑ i ∈ Finset.range (n + 1), i := by
      rw [Nat.range_eq_Icc_zero_sub_one, Nat.add_one_sub_one n]
      have h : Set.Icc 0 0 ∪ Set.Ioc 0 n = Set.Icc 0 n := by
        rw [Set.Icc_union_Ioc_eq_Icc]
        all_goals
          norm_num
      rw [show Set.Ioc 0 n = Set.Icc 1 n by ext x; simp; omega] at h
      rw [<-Finset.coe_Icc, <-Finset.coe_Icc, <-Finset.coe_Icc] at h
      norm_cast at h
      rw [h.symm]
      clear h
      rw [Finset.sum_union]
      all_goals
        simp
    -- Break the iff into two parts.
    apply Iff.intro <;> intro h
    . -- If 1 + 2 + ⋯ + n ∣ 6n, then n = 1, 2, 3, 5 or 11.
      apply Nat.mul_dvd_mul_left 2 at h
      rw [g, Nat.mul_comm, Finset.sum_range_id_mul_two, Nat.add_one_sub_one n, <-mul_assoc] at h
      apply Nat.dvd_of_mul_dvd_mul_right at h
      norm_num at h
      replace h : n + 1 ∣ 12 ∧ 12 ≠ 0 := by
        tauto
      rw [<-Nat.mem_divisors] at h
      -- Use the computer to find the factors of 12 (native_decide is necessary).
      rw [show Nat.divisors 12 = {1, 2, 3, 4, 6, 12} by native_decide] at h
      simp at h
      tauto
      omega
    . -- If n = 1, 2, 3, 5 or 11, then 1 + 2 + ⋯ + n ∣ 6n.
      obtain h | h | h | h | h := h
      all_goals
        rw [g, h]
        rewrite [Finset.sum_range_id]
        norm_num
  have h : {n : ℕ | n ≠ 0 ∧ (∑ i in Finset.Icc 1 n, i) ∣ 6 * n} = {1, 2, 3, 5, 11} := by
    ext n
    simp [-ne_eq]
    apply Iff.intro <;> intro h
    . rw [this] at h
      tauto
      tauto
    . refine ⟨?_, ?_⟩
      omega
      rwa [this]
      omega
  calc
    {n : ℕ | n ≠ 0 ∧ (∑ i in Finset.Icc 1 n, i) ∣ 6 * n}.ncard = Set.ncard {1, 2, 3, 5, 11} := by rw [h]
    _ = Set.ncard {2, 3, 5, 11} + 1 := by rw [Set.ncard_insert_of_not_mem (by simp)]
    _ = Set.ncard {3, 5, 11} + 1 + 1 := by rw [Set.ncard_insert_of_not_mem (by simp)]
    _ = Set.ncard {5, 11} + 1 + 1 + 1 := by rw [Set.ncard_insert_of_not_mem (by simp)]
    _ = Set.ncard {11} + 1 + 1 + 1 + 1 := by rw [Set.ncard_insert_of_not_mem (by simp)]
    _ = 1 + 1 + 1 + 1 + 1 := by rw [Set.ncard_singleton]
    _ = 5 := by norm_num
