import Mathlib

open Finset

/- 2. (1994 Sichuan Province High School Mathematics Competition) Given the set $M=\{1,2, \cdots, k\}$, for $A \subseteq M$, denote the sum of all elements in $A$ as $S(A)$. If $M$ can be divided into two disjoint subsets $A$ and $B$, and $A \cup B=M, S(A)=2 S(B)$. Find all values of $k$.

将上面的文本翻译成英文，请保留源文本的换行和格式，直接输出翻译结果。 -/
theorem number_theory_224046 {k : ℕ} (hk : 0 < k) :
    (∃ A B, A ∩ B = ∅ ∧ Icc 1 k = A ∪ B ∧ ∑ x ∈ A, x = 2 * ∑ x ∈ B, x) ↔ (3 ∣ k ∨ 3 ∣ k + 1) := by
  -- Prove an auxiliary result:
  -- ∑ i ∈ [1, n], i = ∑ i ∈ [0, n + 1), i.
  have haux n : ∑ i ∈ Icc 1 n, i = ∑ i ∈ range (n + 1), i := by
    rw [sum_range_eq_add_Ico, zero_add]
    congr
    exact Nat.zero_lt_succ n
  constructor
  -- Assume that there exist A, B such that A ∩ B = ∅, [1, k] = A ∪ B, and ∑ x ∈ A, x = 2 ∑ x ∈ B, x.
  -- Show that 3 divides k or 3 divides k + 1.
  · intro ⟨A, B, hAB, hM, hsum⟩
    -- It is enough to show that k * (k + 1) = 6 ∑ x ∈ B, x.
    suffices k * (k + 1) = 6 * ∑ x ∈ B, x by
      have h : 3 ∣ k * (k + 1) := by use 2 * ∑ x ∈ B, x; linarith
      rw [Nat.prime_three.dvd_mul] at h
      exact h
    calc
      -- We have k * (k + 1) = 2 ∑ x ∈ [0, k + 1), x
      --                     = 2 ∑ x ∈ [1, k], x
      --                     = 2 (∑ x ∈ A, x + ∑ x ∈ B), x (because [1, k] = A ∪ B and A ∩ B = ∅)
      --                     = 2 (2 ∑ x ∈ B, x + ∑ x ∈ B, x)
      --                     = 6 ∑ x ∈ B, x.
      k * (k + 1) = (k + 1) * (k + 1 - 1) := by rw [mul_comm, show k + 1 - 1 = k by simp]
      _ = (∑ x ∈ range (k + 1), x) * 2 := by rw [sum_range_id_mul_two]
      _ = 2 * ∑ x ∈ Icc 1 k, x := by rw [haux, mul_comm]
      _ = 2 * ∑ x ∈ A ∪ B, x := by rw [hM]
      _ = 2 * (∑ x ∈ A, x + ∑ x ∈ B, x) := by
          rw [sum_union]
          rw [disjoint_iff_inter_eq_empty]
          exact hAB
      _ = 6 * ∑ x ∈ B, x := by
          rw [hsum]
          ring
  · intro h
    cases' h with h h
    -- Assume now that 3 ∣ k and show that there exist A, B with required properties.
    -- 3 ∣ k implies that k = 3 n for some n.
    · have ⟨n, hn⟩ := h
      subst k
      -- Let B = {3 x + 2 | x ∈ [0, n)}.
      set B := (range n).image (fun x => 3 * x + 2)
      -- It is easy to show B ⊆ [1, 3n].
      have hB : B ⊆ Icc 1 (3 * n) := by
        simp [B]
        intro x
        simp only [mem_image, mem_range, mem_Icc, forall_exists_index, and_imp]
        omega
      -- Take A = [1, 3n] \ B.
      use Icc 1 (3 * n) \ B, B
      -- A ∪ B = [1, 3n] and A ∩ B = ∅ follow from the definitions of A and B.
      simp [B, hB]
      -- Show that ∑ x ∈ [1, 3n] \ B, x = 2 ∑ x ∈ B, x.
      apply Nat.add_right_cancel (m := ∑ x ∈ B, x)
      -- It is equivalent to showing that ∑ x ∈ [1, 3n], x = 3 ∑ x ∈ B, x = 3 ∑ x ∈ [0, n), (3 x + 2).
      rw [sum_sdiff hB, haux]
      apply Nat.mul_right_cancel zero_lt_two
      -- 2 ∑ x ∈ [1, 3n] x = 3n (3n + 1).
      rw [sum_range_id_mul_two]
      simp [B]
      -- We compute 2 ∑ x ∈ [0, n), (3 x + 2) = 3n (n - 1) + 4n.
      have eq : (∑ x ∈ range n, (3 * x + 2)) * 2 = 3 * n * (n - 1) + 4 * n := by
        rw [sum_add_distrib, add_mul, ← mul_sum, mul_right_comm, mul_assoc, mul_comm 2]
        simp [sum_range_id_mul_two]
        ring
      -- After simplifications we get 2 ∑ x ∈ [1, 3n], x = 6 ∑ x ∈ B, x.
      rw [mul_comm 2, add_mul, add_mul, eq]
      zify [show 1 ≤ n by omega]
      ring
    -- Assume now that 3 ∣ k + 1 and show that there exist A, B with required properties.
    -- 3 ∣ k + 1 implies that k = 3 n - 1 for some n.
    · replace ⟨n, h⟩ := h
      replace h : k = 3 * n - 1 := by omega
      subst k
      -- Let B = {3 x + 1 | x ∈ [0, n)}.
      set B := (range n).image (fun x => 3 * x + 1)
      -- It is easy to show B ⊆ [1, 3n - 1].
      have hB : B ⊆ Icc 1 (3 * n - 1) := by
        simp [B]
        intro x
        simp only [mem_image, mem_range, mem_Icc, forall_exists_index, and_imp]
        omega
      -- Take A = [1, 3n - 1] \ B.
      use Icc 1 (3 * n - 1) \ B, B
      -- A ∪ B = [1, 3n - 1] and A ∩ B = ∅ follow from the definitions of A and B.
      simp [B, hB]
      -- Show that ∑ x ∈ [1, 3n - 1] \ B, x = 2 ∑ x ∈ B, x.
      apply Nat.add_right_cancel (m := ∑ x ∈ B, x)
      rw [sum_sdiff hB, haux]
      -- It is equivalent to showing that ∑ x ∈ [1, 3n - 1], x = 3 ∑ x ∈ B, x = 3 ∑ x ∈ [0, n), (3 x + 1).
      apply Nat.mul_right_cancel zero_lt_two
      -- 2 ∑ x ∈ [1, 3n - 1] x = 3n (3n - 1).
      rw [sum_range_id_mul_two]
      simp [B]
      -- We compute 2 ∑ x ∈ [0, n), (3 x + 1) = 3n (n - 1) + 2n.
      have eq : (∑ x ∈ range n, (3 * x + 1)) * 2 = 3 * n * (n - 1) + 2 * n := by
        rw [sum_add_distrib, add_mul, ← mul_sum, mul_right_comm, mul_assoc, mul_comm 2]
        simp [sum_range_id_mul_two]
        ring
      -- After simplifications we get 2 ∑ x ∈ [1, 3n - 1], x = 6 ∑ x ∈ B, x.
      rw [mul_comm 2, add_mul, add_mul, eq]
      zify [show 1 ≤ n ∧ 1 ≤ 3 * n by omega]
      ring