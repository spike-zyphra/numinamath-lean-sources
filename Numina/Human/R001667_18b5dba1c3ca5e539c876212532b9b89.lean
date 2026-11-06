import Mathlib

/-3. (USA) Find the integer represented by $\left[\sum_{n=1}^{10^{9}} n^{-2 / 3}\right]$. Here $[x]$ denotes the greatest integer less than or equal to $x$ (e.g. $[\sqrt{2}]=1$ ).-/
theorem other_25059 : ⌊∑ n ∈ (Finset.Icc 1 (10^9) : (Finset ℕ)), (n:ℝ) ^ ((-2:ℝ)/3)⌋ = 2997 := by
-- We first prove the following auxillary identity
  have aux0 : ∀ k : ℝ, 0 < k → (((k + 1) ^ ((2:ℝ)/3)) + (k + 1) ^ ((1:ℝ)/3) * k ^ ((1:ℝ)/3) + k ^ ((2:ℝ)/3)) *
  ((k + 1) ^ ((1:ℝ)/3) - k ^ ((1:ℝ)/3)) = 1 := by
    intro k hk; ring_nf
    repeat rw [← Real.rpow_add, ← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num; ring; any_goals linarith
-- Prove the following auxillary inequality about $k^(-2/3)$, it gives an upper bound of $k^(-2/3)$ telescoping in $k$
  have aux1 : ∀ k : ℝ, 1 ≤ k → k ^ ((-2:ℝ)/3) < 3 * (k ^ ((1:ℝ)/3) - (k - 1) ^ ((1:ℝ)/3)) := by
    intro k hk; by_cases h : k ≤ 1
    · replace h : k = 1 := by linarith
      simp_all
    push_neg at h
    rw [← mul_lt_mul_iff_of_pos_left (show 0 < k ^ ((2:ℝ)/3) by apply Real.rpow_pos_of_pos; linarith)]
    rw [← Real.rpow_add, ← mul_assoc]; norm_num
    nth_rw 1 [← aux0 (k-1) (show _ by linarith)]; norm_num
    rw [mul_lt_mul_iff_of_pos_right, ← sub_lt_sub_iff_right (k^((2:ℝ)/3))]
    ring_nf; rw [mul_two]; apply add_lt_add
    · rw [show (2:ℝ)/3=1/3+1/3 by norm_num, Real.rpow_add, mul_lt_mul_iff_of_pos_left]
      rw [Real.rpow_lt_rpow_iff]; any_goals linarith
      apply Real.rpow_pos_of_pos; linarith
    rw [Real.rpow_lt_rpow_iff]; any_goals linarith
    simp; rw [Real.rpow_lt_rpow_iff]; any_goals linarith
-- Prove the following auxillary inequality about $k^(-2/3)$, it gives a lower bound of $k^(-2/3)$ telescoping in $k$
  have aux2 : ∀ k : ℝ, 0 < k → 3 * ((k + 1) ^ ((1:ℝ)/3) - k ^ ((1:ℝ)/3)) < k ^ ((-2:ℝ)/3) := by
    intro k hk
    rw [← mul_lt_mul_iff_of_pos_left (show 0 < k ^ ((2:ℝ)/3) by apply Real.rpow_pos_of_pos; assumption)]
    rw [← Real.rpow_add, ← mul_assoc]; norm_num
    nth_rw 4 [← aux0 k hk]; rw [mul_lt_mul_iff_of_pos_right, ← sub_lt_sub_iff_right (k^((2:ℝ)/3))]
    ring_nf; rw [mul_two]; apply add_lt_add
    · rw [Real.rpow_lt_rpow_iff]; any_goals linarith
    rw [show (2:ℝ)/3=1/3+1/3 by norm_num, Real.rpow_add, mul_lt_mul_iff_of_pos_right]
    rw [Real.rpow_lt_rpow_iff]; any_goals linarith
    apply Real.rpow_pos_of_pos; assumption
    simp; rw [Real.rpow_lt_rpow_iff]; any_goals linarith
-- Prove that we can get Finset.Icc 1 by isolating $0$ from Finset.range (10^9+1), we will use this to rewrite summations later
  have iso0 : Finset.range 1000000001 = {0} ∪ Finset.Icc 1 1000000000 := by
    ext i; simp; constructor; any_goals intro h'
    · by_contra h; push_neg at h; rcases h with ⟨hl,hr⟩
      rw [Nat.ne_zero_iff_zero_lt] at hl
      replace hr := hr (show _ by linarith); linarith
    rcases h' with h'|h'; any_goals linarith
-- Use Int.floor_eq_iff to rewrite the final goal and split it to two inequalities
  rw [Int.floor_eq_iff]; push_cast; norm_num; constructor
-- To prove the lower bound, we apply aux2 and write out a summation version of aux2
  · have h0 : ∑ x ∈ (Finset.Icc 1 1000000000 : Finset ℕ), 3 * ((((x + 1):ℕ):ℝ) ^ ((1:ℝ) / 3) - x ^ ((1:ℝ) / 3)) <
    ∑ x ∈ (Finset.Icc 1 1000000000 : Finset ℕ), (x:ℝ) ^ (-(2:ℝ) / 3) := by
      apply Finset.sum_lt_sum_of_nonempty; use 1; simp
      intro k hk; push_cast; simp at hk
      apply aux2; simp; linarith
    rw [← Finset.mul_sum] at h0
  -- Apply Finset.sum_range_sub to simplify the telescoping sum on the LHS and finish the final goal
    have h1 := Finset.sum_range_sub (fun n => (n : ℝ) ^ ((1:ℝ)/3)) 1000000001
    rw [iso0, Finset.sum_union] at h1; simp at h1 h0
    rw [← @sub_left_inj _ _ 1] at h1; simp at h1
    rw [h1] at h0; suffices : (2997:ℝ) < 3 * (1000000001 ^ (3:ℝ)⁻¹ - 1)
    · rw [← neg_div]; linarith
    rw [← div_lt_iff', ← add_lt_add_iff_right 1]; norm_num
    rw [← Real.rpow_lt_rpow_iff _ _ (show 0<(3:ℝ) by norm_num), ← Real.rpow_mul]
    norm_num; any_goals linarith
    apply Real.rpow_nonneg; norm_num
    rw [Disjoint]; simp
-- To prove the upper bound, we isolate the first term in the summation, then for the rest terms, we apply aux2 and write out a summation version of aux2
  have h0 : ∑ x ∈ (Finset.Icc 1 1000000000 : Finset ℕ), (x:ℝ) ^ (-(2:ℝ) / 3) <
  1 + ∑ x ∈ (Finset.Icc 2 1000000000 : Finset ℕ), 3 * (((((x+1):ℕ):ℝ)-1) ^ ((1:ℝ) / 3) - ((x-1) ^ ((1:ℝ) / 3))) := by
    rw [← Nat.Icc_insert_succ_left, Finset.sum_insert]; simp
    apply Finset.sum_lt_sum_of_nonempty; use 2; simp
    intro k hk; simp at hk aux1
    apply aux1; simp; linarith
    simp; norm_num
  rw [← Finset.mul_sum] at h0
-- Apply Finset.sum_range_sub to simplify the telescoping sum and finish the final goal
  have h1 := Finset.sum_range_sub (fun n => ((n : ℝ)-1) ^ ((1:ℝ)/3)) 1000000001
  rw [iso0, Finset.sum_union] at h1; simp at h1
  apply_fun (fun t => (-1:ℝ) ^ (3:ℝ)⁻¹ + t) at h1; simp at h1 h0
  rw [← Nat.Icc_insert_succ_left, Finset.sum_insert] at h1; simp at h1
  rw [show (1000000001:ℝ)-1=10^(9:ℝ) by norm_num, ← Real.rpow_mul] at h1
  rw [add_sub_assoc, add_comm, ← @sub_left_inj _ _ 1] at h1; simp at h1
  rw [h1] at h0; norm_num at h0; assumption; any_goals simp
