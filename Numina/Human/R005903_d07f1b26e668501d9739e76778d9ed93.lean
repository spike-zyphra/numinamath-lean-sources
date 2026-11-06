import Mathlib

/-On an $8 \times 8$ chessboard, 6 black rooks and $k$ white rooks are placed on different cells so that each rook only attacks rooks of the opposite color. Compute the maximum possible value of $k$.
(Two rooks attack each other if they are in the same row or column and no rooks are between them.)-/

lemma my_bound (N : ℕ) (B_total : ℕ)
    (num_B_in_row num_W_in_row : ℕ → ℕ) -- Functions mapping row index to rook count
    -- Axiom 1: Sum of black rooks per row equals B_total
    (h_sum_B : ∑ i in Finset.range N, num_B_in_row i = B_total)
    -- Lemma 1 (Axiom): If b_i = 0, then w_i ≤ 1
    (h_lemma1 : ∀ i, i < N → num_B_in_row i = 0 → num_W_in_row i ≤ 1)
    -- Lemma 2 (Axiom): If b_i > 0, then w_i ≤ b_i + 1
    (h_lemma2 : ∀ i, i < N → num_B_in_row i > 0 → num_W_in_row i ≤ num_B_in_row i + 1) :
    (∑ i in Finset.range N, num_W_in_row i) ≤ B_total + N := by
  let R_all := Finset.range N
  let R_B_pos := R_all.filter (fun i => num_B_in_row i > 0)
  let R_B_zero := R_all.filter (fun i => num_B_in_row i = 0)

  have R_all_eq_union_disjoint : R_all = R_B_pos ∪ R_B_zero := by
    ext i
    simp only [R_B_pos, R_all, R_B_zero, Finset.mem_range, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro h_mem_range_N 
      simp only [h_mem_range_N, true_and, implies_true]
      refine Or.symm (Nat.eq_zero_or_pos (num_B_in_row i))
    · intro h_mem_union 
      rcases h_mem_union with (h | h) <;> exact h.1

  have R_B_disjoint : Disjoint R_B_pos R_B_zero := by
    -- If an element is in both, it must satisfy (num_B_in_row i > 0) and (num_B_in_row i = 0)
    -- which is a contradiction.
    simp  [R_B_pos, R_B_zero, R_all]
    have := Finset.disjoint_filter_filter_neg (Finset.range N) (Finset.range N) (fun i => 0 < num_B_in_row i)
    simp at this
    exact this
    
  -- Split the sum over R_all
  have : Finset.range N = R_all := by simp
  -- rw[← h_sum_B, this]
  rw [this, R_all_eq_union_disjoint, Finset.sum_union R_B_disjoint]
  -- rw [Finset.sum_union R_B_disjoint]
  
  have sum_b_in_R_B_pos_eq_total_B : ∑ i in R_B_pos, num_B_in_row i = B_total := by
    rw [← h_sum_B, this] -- Start from B_total = ∑ i in R_all ...
    rw [R_all_eq_union_disjoint, Finset.sum_union R_B_disjoint]
    -- We have B_total = (∑ i in R_B_pos, num_B_in_row i) + (∑ i in R_B_zero, num_B_in_row i)
    -- Show that the sum over R_B_zero is 0
    have sum_b_in_R_B_zero_is_zero : ∑ i in R_B_zero, num_B_in_row i = 0 := by
      apply Finset.sum_eq_zero_iff.mpr -- More direct way to prove sum is zero
      intros x hx_in_R_B_zero
      exact (Finset.mem_filter.mp hx_in_R_B_zero).2 -- .2 is the condition num_B_in_row x = 0
    rw [sum_b_in_R_B_zero_is_zero, add_zero]

  have partition_N : N = ∑ i in R_B_pos, 1 + ∑ i in R_B_zero, 1 := by
    -- rw [Finset.sum_add_distrib]
    simp [R_B_pos, R_B_zero, R_all]
    rw [← Finset.card_union_of_disjoint R_B_disjoint, ← R_all_eq_union_disjoint]
    simp[R_all]
  
  rw[← sum_b_in_R_B_pos_eq_total_B, partition_N]
  rw[← add_assoc]
  rw [← Finset.sum_add_distrib]
  
  -- Apply bounds using the lemmas
  apply Nat.add_le_add
  · -- Sum over R_B_pos (rows where b_i > 0)
    apply Finset.sum_le_sum
    intros i hi_mem
    -- Deconstruct hi_mem to get properties of i
    obtain ⟨h_i_in_range, h_b_i_pos⟩ := (Finset.mem_filter).mp hi_mem
    exact h_lemma2 i (by simp [R_all] at h_i_in_range; assumption) h_b_i_pos
  · -- Sum over R_B_zero (rows where b_i = 0)
    apply Finset.sum_le_sum
    intros i hi_mem
    obtain ⟨h_i_in_range, h_b_i_zero⟩ := (Finset.mem_filter).mp hi_mem
    exact h_lemma1 i (by simp [R_all] at h_i_in_range; assumption) h_b_i_zero

theorem combinatorics_610630 :
    ∀ (num_B_in_row num_W_in_row : ℕ → ℕ)
      (h_sum_B_specific : ∑ i in Finset.range 8, num_B_in_row i = 6)
      (h_lemma1_specific : ∀ i, i < 8 → num_B_in_row i = 0 → num_W_in_row i ≤ 1)
      (h_lemma2_specific : ∀ i, i < 8 → num_B_in_row i > 0 → num_W_in_row i ≤ num_B_in_row i + 1),
    (∑ i in Finset.range 8, num_W_in_row i) ≤ 14 := by
  intros num_B_in_row_inst num_W_in_row_inst h_sum_B_inst h_lemma1_inst h_lemma2_inst

  have general_bound_applied := my_bound 8 6
    num_B_in_row_inst num_W_in_row_inst
    h_sum_B_inst h_lemma1_inst h_lemma2_inst

  convert general_bound_applied
