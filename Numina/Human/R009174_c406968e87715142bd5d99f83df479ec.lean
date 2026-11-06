import Mathlib

/-- Checks if `k` can be expressed as a sum of squares of distinct numbers at most `sMax`. -/
def checkIfSumOfSquares (k : ℕ) (sMax : ℕ) : Bool :=
  match k, sMax with
  | 0, _ => true
  | _, 0 => false
  | _, a + 1 =>
    if k ≥ sMax^2 then
      if checkIfSumOfSquares (k - sMax^2) a then
        true
      else
        checkIfSumOfSquares k a
    else
      checkIfSumOfSquares k a

set_option maxHeartbeats 500000 in
theorem Number_Theory_7513 : Set.Finite {n : ℕ | n > 0 ∧ ¬∃ s : Finset ℕ, ∑ i ∈ s, i^2 = n} := by
  have exists_of_checkIfSumOfSquares (m : ℕ) (h : checkIfSumOfSquares m (m.sqrt + 1) = true) : ∃ s, ∑ i ∈ s, i^2 = m := by
    have (k sMax : ℕ) (h : checkIfSumOfSquares k sMax = true) : ∃ s, (∀ i ∈ s, i ≤ sMax) ∧ ∑ i ∈ s, i^2 = k := by
      induction' k using Nat.strong_induction_on with k ih generalizing sMax
      cases' k with k
      · use ∅
        simp
      induction' sMax with a aih
      · simp [checkIfSumOfSquares] at h
      simp [checkIfSumOfSquares] at h
      split_ifs at h
      · rcases h with (h | h)
        · obtain ⟨s, hs1, hs2⟩ := ih (k + 1 - (a + 1)^2) (by simp) a h
          use insert (a + 1) s
          constructor
          · intro i hi
            simp at hi
            rcases hi with (hi | hi)
            · omega
            · linarith [hs1 i hi]
          · rw [Finset.sum_insert]
            · omega
            intro h
            simpa using hs1 _ h
        · obtain ⟨s, hs1, hs2⟩ := aih h
          use s
          refine ⟨?_, hs2⟩
          intro i hi
          linarith [hs1 i hi]
      · obtain ⟨s, hs1, hs2⟩ := aih h
        use s
        refine ⟨?_, hs2⟩
        intro i hi
        linarith [hs1 i hi]
    obtain ⟨s, _, hs⟩ := this m (m.sqrt + 1) h
    use s
  -- It can be directly checked that every odd integer $67<$ $n \leq 211$ can be represented as a sum of distinct squares.
  have h1 : ∀ n, Odd n → (67 < n) → (n ≤ 211) → ∃ s, ∑ i ∈ s, i^2 = n := by
    intro n h_odd hn hn'
    have h_step {m : ℕ} (a : ℕ) (h_le : a^2 ≤ m) (s) (hs : ∑ i ∈ s, i^2 = m - a^2) (h_mem : a ∉ s) : ∑ i ∈ insert a s, i^2 = m := by
      rwa [Finset.sum_insert h_mem, Nat.add_comm, Nat.Simproc.add_eq_le _ h_le]
    rw [Nat.odd_iff] at h_odd
    interval_cases n <;> norm_num at h_odd <;> clear h_odd hn hn'
    all_goals
      apply exists_of_checkIfSumOfSquares; repeat (dsimp [checkIfSumOfSquares] <;> norm_num1)
  suffices h : ∀ n, 211 < n → ∃ s, ∑ i ∈ s, i^2 = n by
    apply Set.Finite.subset (Set.finite_le_nat 211)
    intro n
    simp only [gt_iff_lt, Set.mem_setOf_eq, and_imp]
    intro _ hn
    specialize h n
    contrapose! hn
    exact h hn
  -- For any $n>211$ we can choose an integer $m$ such that $m^{2}>\frac{n}{2}$ and $n-m^{2}$ is odd and greater than 67,
  have h2 : ∀ n, 211 < n → ∃ m, m^2 > n / 2 ∧ n - m^2 > 67 ∧ Odd (n - m^2) := by
    intro n hn
    have hm1 : ((n / 2).sqrt + 1)^2 > n / 2 := by
      have := Nat.succ_le_succ_sqrt' (n / 2)
      omega
    have hm2_aux (hn' : 400 < n) : (n / 2).sqrt ≤ n / 24 := by
      rw [← Nat.sqrt_eq' (n / 24)]
      apply Nat.sqrt_le_sqrt
      simp_rw [← Nat.floor_div_eq_div (α := ℚ)]
      simp
      apply Nat.floor_le_of_le
      simp
      replace hn' : 400 < (n : ℚ) := by exact Nat.ofNat_lt_cast.mpr hn'
      trans ((n : ℚ) / 24 - 1) ^ 2
      · nlinarith
      · apply pow_le_pow_left
        · linarith
        · linarith [Nat.lt_floor_add_one ((n : ℚ) / 24)]
    have hm2 : (n - ((n / 2).sqrt + 2)^2) > 67 := by
      by_cases hn' : 400 < n
      · simp [add_sq]
        ring_nf
        have := Nat.sqrt_le' (n / 2)
        omega
      · interval_cases n <;> norm_num
    by_cases h_odd : Odd (n - ((n / 2).sqrt + 1)^2)
    · use (n / 2).sqrt + 1
      constructorm* _ ∧ _
      · exact hm1
      · calc
          _ ≥ n - ((n / 2).sqrt + 2) ^ 2 := by
            simp only [ge_iff_le]
            apply Nat.sub_le_sub_left
            apply Nat.pow_le_pow_of_le_left
            simp
          _ > _ := hm2
      · exact h_odd
    · replace h_odd : Odd (n - ((n / 2).sqrt + 2)^2) := by
        contrapose! h_odd
        simp at h_odd
        rw [show (n / 2).sqrt + 2 = (n / 2).sqrt + 1 + 1 by omega, add_pow_two] at h_odd
        simp at h_odd
        have : ((n / 2).sqrt + 1 + 1) ^ 2 ≤ n := by
          ring_nf
          have := Nat.sqrt_le' (n / 2)
          by_cases hn' : 400 < n
          · omega
          · interval_cases n <;> norm_num
        rw [add_pow_two] at this
        rw [show n - ((n / 2).sqrt + 1) ^ 2 = n - (((n / 2).sqrt + 1) ^ 2 + 2 * ((n / 2).sqrt + 1) + 1) + (2 * ((n / 2).sqrt + 1) + 1) by omega]
        rw [Nat.add_comm]
        apply Even.odd_add h_odd
        rw [Nat.add_comm]
        exact Even.odd_add (by simp) (by simp)
      use (n / 2).sqrt + 2
      constructorm* _ ∧ _
      · calc
          _ ≥ ((n / 2).sqrt + 1) ^ 2 := by simp; apply Nat.pow_le_pow_of_le_left; simp
          _ > _ := hm1
      · exact hm2
      · exact h_odd
  -- and therefore by the induction hypothesis can be written as a sum of distinct squares.
  -- Hence $n$ is also a sum of distinct squares.
  intro n hn
  induction' n using Nat.strong_induction_on with n ih
  obtain ⟨m, hm, hm', h_odd⟩ := h2 n hn
  obtain ⟨s, hs⟩ : ∃ s, ∑ i ∈ s, i^2 = n - m^2 := by
    by_cases h : n - m^2 ≤ 211
    · exact h1 (n - m^2) h_odd (by omega) h
    · exact ih (n - m^2) (by omega) (by omega)
  use insert m s
  rw [Finset.sum_insert, hs]
  · omega
  intro h_mem
  rw [← Finset.add_sum_erase _ _ h_mem] at hs
  omega