import Mathlib

/- Let us consider the sequence $1,2, 3, \ldots , 2002$. Somebody choses $1002$ numbers from the sequence. Prove that there are two of the chosen numbers which are relatively prime (i.e. do not have any common divisors except $1$). -/
theorem number_theory_45620 (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 2002)
    (hS1 : S.card = 1002) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ Nat.Coprime a b := by

    -- Consider the sequence (1, 2, 3, \ldots, 2002).
    -- Group the sequence into pairs: ({1, 2}, {3, 4}, \ldots, {2001, 2002}). There are (1001) such pairs.
    -- For each such pair (2n - 2, 2n), we use n as its representative.
    -- So these 1001 pairs is represented by T = [1, 1001].
    let T : Finset ℕ := Finset.Icc 1 1001

    -- According to the problem, (1002) numbers are chosen from the sequence, which is larger than the size of T
    have hT_card_le : T.card * 1 < S.card := by simp [T, hS1]

    -- By the Pigeonhole Principle, if (1002) numbers are chosen from (1001) pairs, at least one pair must have both of its numbers chosen. This is because there are more numbers chosen than there are pairs.
    let f : ℕ → ℕ := fun n ↦ (n + 1) / 2
    have hf_mem : ∀ a ∈ S, f a ∈ T := by
      intro a amem
      have : a ∈ Finset.Icc 1 2002 := by
        exact hS amem
      simp at this
      simp [T, f]
      constructor
      · exact Nat.le_avg_right this.1
      · by_cases h : a ≤ 2001
        · apply Nat.div_le_of_le_mul
          norm_num
          exact Nat.succ_le_succ h
        · have : a = 2002 := by linarith
          rw [this]

    -- Let the pair (2y - 1, 2y) be such that both numbers are chosen
    have ⟨y, ymem, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf_mem hT_card_le
    apply Finset.one_lt_card.mp at hy

    -- that is, there are a ≠ b ∈ S such that y = ⌊(a + 1) / 2⌋ = ⌊(b + 1) / 2⌋
    obtain ⟨a, amem, b, bmem, hne⟩ := hy
    simp [f] at amem bmem

    -- we will show that a, b are coprime
    use a, amem.1, b, bmem.1, hne

    clear hT_card_le ymem T hf_mem f

    -- wlog we can assume a > b
    wlog h : a > b
    · push_neg at h
      have h' : b > a := lt_of_le_of_ne h hne
      have := this S hS hS1 y b a hne.symm bmem amem h'
      apply Nat.Coprime.symm
      exact this

    -- in this case we prove that b = a + 1
    have h_a_succ_le : a + 1 ≤ 2 * y + 1 := by
      by_contra! h
      have : a + 1 ≥ 2 * y + 2 := by exact h
      have : (a + 1) / 2 ≥ (2 * y + 2) / 2 := by exact Nat.div_le_div_right h
      rw [show 2 * y + 2 = (y + 1) * 2 by ring, Nat.mul_div_cancel] at this
      linarith
      norm_num

    have ha_le : a ≤ 2 * y := by exact Nat.le_of_lt_succ h_a_succ_le

    have h_b_succ_ge_a : b + 1 ≥ a := by
      by_contra! h
      have : b + 1 < 2 * y := by exact Nat.lt_of_lt_of_le h ha_le
      rw [mul_comm] at this
      have : (b + 1) / 2 < y * 2 / 2 := by
        refine Nat.div_lt_div_of_lt_of_dvd ?_ this
        exact Nat.dvd_mul_left 2 y
      rw [Nat.mul_div_cancel] at this
      linarith
      norm_num

    have : a = b + 1 := by linarith
    rw [this]

    -- Then it follows from that any two consecutive numbers are coprime.
    simp only [Nat.coprime_self_add_left, Nat.coprime_one_left_eq_true]
