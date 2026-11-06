import Mathlib
open Finset Set Nat
noncomputable section

-- Define $N_i$,$S_m$.
def N_i (i : ℕ) := ∑ k ∈ Finset.range i, 2^k

def S_m (m : ℕ) := ∑ i ∈ Finset.range m, N_i (i + 1)

-- Prove that $N_i$ equals $2^i - 1$ using a lemma.
lemma N_i_geometric (i : ℕ) : N_i i = 2^i - 1 := by
  have h_N_i : N_i i = ∑ k ∈ Finset.range i, 2^k := by rfl
  have h_geom : ∑ k ∈ Finset.range i, 2^k = 2^i - 1 := by
    have : 2^i - 1 = (2^i - 1)/(2 - 1) := by norm_num
    rw [this]
    exact Nat.geomSum_eq (by nlinarith) i
  rw [h_N_i, h_geom]

/-Let $m$ be a positive integer. Let $N_i$ denote the number which in base 2 consists of $i$ digits, all of which are $1$. For example, $N_2 = 11_2 = 1 \cdot 2^1 + 1 \cdot 2^0 = 3$. Compute the sum $S_m = \sum_{i=1}^{m} N_i$. Show that the sum $S_m$ is equal to $2^{m+1} - m - 2$.-/
theorem number_theory_638351 (m : ℕ) (hm : m > 0) : S_m m = 2^(m + 1) - m - 2 := by
  -- Expand $S_m = ∑ (2^(i+1) - 1)$.
  have h_S_m : S_m m = ∑ i ∈ Finset.range m, (2^(i + 1) - 1) := by
    unfold S_m
    apply Finset.sum_congr rfl
    intro i _
    rw [N_i_geometric (i + 1)]
  -- Decompose the sum.
  have h_split : S_m m = (∑ i ∈ Finset.range m, 2^(i + 1)) - (∑ i ∈ Finset.range m, 1) := by
    rw [h_S_m]
    rw [Finset.sum_tsub_distrib]
    simp [Fin.sum_const]
    intro x hx
    simp [Nat.one_le_pow (x + 1) 2 (by norm_num)]
  -- Compute the geometric series $∑ 2^(i+1)$.
  have h_geom_sum : ∑ i ∈ Finset.range m, 2^(i + 1) = 2^(m + 1) - 2 := by
    have h_shift : ∑ i ∈ Finset.range m, 2^(i + 1) = ∑ i ∈ Finset.Ico 1 (m + 1), 2^i := by
      rw [Finset.sum_Ico_eq_sum_range]
      · apply Finset.sum_congr
        · ext i
          simp [Finset.mem_Ico, Nat.one_le_iff_ne_zero]
        · intros; rw [add_comm]
    have h_geom : ∑ i ∈ Finset.Ico 1 (m + 1), 2^i = (∑ i ∈ Finset.range (m + 1), 2^i) - (∑ i ∈ Finset.range 1, 2^i) := by
      have h_le : 1 ≤ m + 1 := by linarith [hm]
      have h_sum : ∑ i ∈ Finset.range 1, 2^i + ∑ i ∈ Finset.Ico 1 (m + 1), 2^i = ∑ i ∈ Finset.range (m + 1), 2^i := by
        rw [Finset.sum_range_add_sum_Ico _ h_le]
      omega
    have h_full : ∑ i ∈ Finset.range (m + 1), 2^i = 2^(m + 1) - 1 := by
      have : 2^(m + 1) - 1 = (2^(m + 1) - 1)/(2 - 1) := by norm_num
      rw [this]
      exact Nat.geomSum_eq (by nlinarith) (m + 1)
    have h_one : ∑ i ∈ Finset.range 1, 2^i = 2^0 := by
      rw [Finset.sum_range_one]
    rw [h_shift, h_geom, h_full, h_one]
    simp
    norm_num [Nat.sub_sub]
  -- Compute the constant sum $∑ 1$.
  have h_const_sum : ∑ i ∈ Finset.range m, 1 = m := by
    rw [Finset.sum_const, Finset.card_range]
    norm_num
  -- Combine results.
  have h_final : S_m m = 2^(m + 1) - m - 2 := by
    rw [h_split, h_geom_sum, h_const_sum]
    omega
  exact h_final
