import Mathlib

/- Task 2. (10 points) A finite increasing sequence $a_{1}, a_{2}, \ldots, a_{n}$ ( $n \geq 3$ ) of natural numbers is given, and for all $k \leq n-2$, the equality $a_{k+2}=3 a_{k+1}-2 a_{k}-2$ holds. The sequence must contain $a_{k}=2022$. Determine the maximum number of three-digit numbers, divisible by 4, that this sequence can contain. -/
theorem algebra_212761: IsGreatest { n | ∃ a: (ℕ → ℕ),
  (∀ k, a (k + 2) = 3 * a (k + 1) - 2 * a k - 2) ∧ (∃ k, a k = 2022) ∧
  {j | ∃ k, a k = j ∧ j ∈ Finset.Icc 100 999 ∧ 4 ∣ j}.ncard = n
} 225 := by
  let mul_4_plus_100: ℕ ↪ ℕ := {
    toFun: ℕ → ℕ := λ n ↦ 4 * n + 100
    inj': ∀ a b: ℕ, 4*a + 100 = 4*b + 100 → a = b := by omega
  }
  -- The set of 3-digit multipls of 4
  let S := Finset.map mul_4_plus_100 (Finset.range 225)
  -- There are precisely 225 3-digit multiples of 4
  have h_S_card: (S.toSet).ncard = 225 := by simp [Set.ncard_eq_toFinset_card]; unfold S; simp
  -- For any sequence a, the set of 3-digit multipls of 4 in a is a subset of all 3-digit multiples of 4
  -- We also use this result to show that the 3-digit multiples of 4 in the sequence a_k = 2k is precisely S
  -- Since it is used twice in the proof, we prove it separately here
  have h_subset (a : ℕ → ℕ): {j | ∃ k, a k = j ∧ j ∈ Finset.Icc 100 999 ∧ 4 ∣ j} ⊆ S := by
    intro j ⟨k, ⟨h_eq, ⟨h_range, h_mul⟩⟩⟩
    apply Finset.mem_map.mpr
    obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le (Finset.mem_Icc.mp h_range).left
    rw [hs] at h_mul
    obtain ⟨t, ht⟩ := (Nat.dvd_add_iff_right (by decide)).mpr h_mul
    use t
    and_intros
    have := (Finset.mem_Icc.mp h_range).right
    apply Finset.mem_range.mpr (by linarith)
    simp [mul_4_plus_100]
    rw [hs, ht, add_comm]
  rw [IsGreatest.eq_1]
  and_intros
  -- We define an arithmetic progression a with difference d = 2, defined by the formula a_k = 2k
  use λ n ↦ 2 * n
  and_intros
  -- This satisfies the equation a_{k + 2} = 3a_{k + 1} - 2a_k - 2
  beta_reduce
  omega
  -- The sequence contains 2022
  use 1011
  -- And all of the 3-digit multipls of 4
  rw [show {j | ∃ k, (fun n ↦ 2 * n) k = j ∧ j ∈ Finset.Icc 100 999 ∧ 4 ∣ j} = S from by
    ext j
    constructor
    apply h_subset
    unfold S
    intro h_j_mem
    norm_cast at h_j_mem
    rw [Finset.mem_map] at h_j_mem
    -- A 3-digit multiple of 4 is of the form 4k + 100
    rcases h_j_mem with ⟨k, ⟨h_k_bound, h_k_eq⟩⟩
    simp [mul_4_plus_100] at h_k_eq
    -- which is the (2k + 50)th term of the sequence
    use (2 * k + 50)
    and_intros
    rw [← h_k_eq]
    ring
    apply Finset.mem_range.mp at h_k_bound
    apply Finset.mem_Icc.mpr
    exact ⟨by linarith, by linarith⟩
    omega
  ]
  exact h_S_card
  rw [upperBounds.eq_1]
  -- Consider an arbitrary sequence satisfyingthe conditions in the problem
  intro n ⟨a, ⟨h_a_rec, ⟨h_2022, h_mul_4⟩⟩⟩
  rw [← h_mul_4]
  -- Then at most it can contain all of the 3-digit multiples of 4
  apply le_trans (Set.ncard_le_ncard $ h_subset a)
  -- and there are 225 of them
  rw [h_S_card]