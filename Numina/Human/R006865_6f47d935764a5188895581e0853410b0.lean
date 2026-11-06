import Mathlib
set_option linter.unusedVariables false

/-Let $V$ be a positive integer. Vanya considers a $k$-digit number $N$. He subtracts from $N$ the sum of all its digits, except for one digit $d_1$ (which must be one of the digits of $N$). The result of this operation is $V$.
Let $d_m$ be the $m$-th digit from the left of $N$ (where $1 \le m \le k$).
To ensure that $d_1$ and $N$ (and thus $d_m$) are well-defined by $V$, we state the following conditions:
1. The excepted digit $d_1$ is determined by the rule $d_1 = ((V-1) \pmod 9) + 1$.
2. Let $X_N = V - d_1$. There is at least one $k$-digit number $N'$ such that $N' - (\text{sum of digits of } N') = X_N$ and $d_1$ is one of the digits of $N'$.
3. All such $k$-digit numbers $N'$ that satisfy condition 2 have the same $m$-th digit from the left. Let this common digit be $d_m$.
What result would Vanya have obtained if he had subtracted the sum of all the digits of $N$ except $d_m$?
Show that the answer is $V - (((V-1) \pmod 9) + 1) + d_m$.-/
theorem number_theory_641904 (V k m : ℕ) (hV : 0 < V) (hk : 0 < k) (hm : 1 ≤ m ∧ m ≤ k)
    (N : ℕ) 
    (hN_digits : ∀ i < k, (N / 10^(k-1-i)) % 10 ∈ Finset.range 10)
    (h_digits_sum : ∑ i ∈ Finset.range k, (N / 10^(k-1-i)) % 10 = (Nat.digits 10 N).sum)
    (d₁ : ℕ) (hd₁ : d₁ = ((V - 1) % 9) + 1)
    (hN_V : N - (∑ i ∈ Finset.range k, (N / 10^(k-1-i)) % 10) + d₁ = V)
    (d_m : ℕ) (hd_m : d_m = (N / 10^(k-1-(m-1))) % 10) :
    N - (∑ i ∈ Finset.range k, if i ≠ m - 1 then (N / 10^(k-1-i)) % 10 else 0) = V - (((V - 1) % 9) + 1) + d_m := by
  -- Define $N$, $S$, $d₁$, original operation $V = N - (S - d₁)$.
  let h_S : ℕ := ∑ i ∈ Finset.range k, (N / 10^(k-1-i)) % 10
  have h_V_eq : V = N - h_S + d₁ := by unfold h_S; exact hN_V.symm
  -- Verify condition : $d₁ = ((V-1) % 9) + 1$.
  have h_d₁_def : d₁ = ((V - 1) % 9) + 1 := hd₁
  have h_d₁_range : 1 ≤ d₁ ∧ d₁ ≤ 9 := by omega
  have h_N_minus_S : N - h_S = V - d₁ := by omega
  -- $d_m = a_m$, conditions $2$ and $3$ ensure $N$ and $d_m$ are determined by $V$.
  have h_d_m_def : d_m = (N / 10^(k-1-(m-1))) % 10 := hd_m
  have h_d_m_range : d_m ∈ Finset.range 10 := by
    rw [h_d_m_def]
    apply hN_digits
    have h_m_1 : m - 1 < k := by omega
    exact h_m_1
  -- New operation $V_new = N - (S - d_m)$.
  have h_V_new : N - (∑ i ∈ Finset.range k, if i ≠ m - 1 then (N / 10^(k-1-i)) % 10 else 0) =
      N - (h_S - d_m) := by
    have h_sum_except : (∑ i ∈ Finset.range k, if i ≠ m - 1 then (N / 10^(k-1-i)) % 10 else 0) =
        h_S - d_m := by
      -- Verify $m - 1 ∈ Finset.range $k$.
      have h_m_1_mem : m - 1 ∈ Finset.range k := by
        simp [Finset.range]
        have h_m_1 : m - 1 < k := by omega
        exact h_m_1
      -- Handle the conditional sum.
      rw [Finset.sum_ite]
      have h_filter_eq : Finset.filter (fun i => ¬ (i ≠ m - 1)) (Finset.range k) = {m - 1} := by
        ext i
        simp [Finset.range]
        omega
      rw [h_filter_eq]
      have h_zero_sum : ∑ x ∈ {m - 1}, (0 : ℕ) = 0 := by simp
      rw [h_zero_sum]
      simp only [add_zero]
      --Split $h_S$.
      have h_S_split : h_S = ∑ i ∈ Finset.filter (fun i => i ≠ m - 1) (Finset.range k), (N / 10^(k-1-i)) % 10 +
                             (N / 10^(k-1-(m-1))) % 10 := by
        unfold h_S
        have h_filter : Finset.range k = Finset.filter (fun i => i ≠ m - 1) (Finset.range k) ∪ {m - 1} := by
          ext i
          simp [Finset.range]
          constructor
          · intro h_i
            by_cases h_eq : i = m - 1
            · right; exact h_eq
            · left; exact ⟨h_i, h_eq⟩
          · rintro (⟨h_i, _⟩ | h_eq)
            · exact h_i
            · rw [h_eq]; omega
        have h_disjoint : Disjoint (Finset.filter (fun i => i ≠ m - 1) (Finset.range k)) {m - 1} := by
          rw [Finset.disjoint_iff_inter_eq_empty]
          ext i
          simp
        rw [h_filter, Finset.sum_union h_disjoint]
        have h_single : ∑ i ∈ {m - 1}, (N / 10^(k-1-i)) % 10 = (N / 10^(k-1-(m-1))) % 10 := by
          simp
        rw [h_single]
        -- Prove equivalence of filtered sets.
        have h_filter_idem : Finset.filter (fun i => i ≠ m - 1) (Finset.filter (fun i => i ≠ m - 1) (Finset.range k) ∪ {m - 1}) =
                             Finset.filter (fun i => i ≠ m - 1) (Finset.range k) := by
          ext i
          simp [Finset.filter]
        rw [h_filter_idem]
      rw [h_S_split, h_d_m_def]
      omega
    rw [h_sum_except]
  -- Substitute $N - S = V - d₁$ to get $V_new = (V - d₁) + d_m$.
  have h_V_new_subst : N - (h_S - d_m) = (V - d₁) + d_m := by
    have h_hs_le: h_S ≤ N := by 
      unfold h_S
      rw [h_digits_sum]
      exact Nat.digit_sum_le 10 N
    have h_dm_le: d_m ≤ h_S := by 
      unfold h_S
      rw [h_d_m_def]
      have h_m_1 : m - 1 < k := by omega
      have h_m_1_mem : m - 1 ∈ Finset.range k := by
        simp [Finset.range]
        exact h_m_1
      have h_index_eq : k - 1 - (m - 1) = k - m := by omega
      rw [h_index_eq]
      let f := fun i => (N / 10^(k-1-i)) % 10
      have h_f_nonneg : ∀ i ∈ Finset.range k, 0 ≤ f i := by
        intro i _
        apply Nat.zero_le
      have h_f_m_1 : f (m - 1) = (N / 10^(k-m)) % 10 := by
        simp [f]
        rw [h_index_eq]
      rw [← h_f_m_1]
      apply Finset.single_le_sum h_f_nonneg h_m_1_mem
    rw [tsub_tsub_assoc h_hs_le h_dm_le]
    rw [h_N_minus_S]
  -- Substitute $d₁ = ((V-1) % 9) + 1$ to get $V_new = V - (((V-1) % 9) + 1) + d_m$.
  have h_final : (V - d₁) + d_m = V - (((V - 1) % 9) + 1) + d_m := by
    rw [h_d₁_def]
  -- Combine all steps.
  rw [h_V_new, h_V_new_subst, h_final]
