import Mathlib

/- How many integers $N$ less than $1000$ can be written as the sum of $j$ consecutive positive odd integers from exactly 5 values of $j\ge 1$? -/
theorem number_theory_93204 :
    Set.ncard {N : ℕ | N < 1000 ∧ {j | ∃ t, Odd t ∧ N = ∑ i ∈ Finset.range j, (t + 2 * i)}.ncard = 5} = 15 := by
  -- show that ∑ i ∈ [0, j), (t + 2 * i) = j * (j - 1 + t)
  have hsum j t : ∑ i ∈ Finset.range j, (t + 2 * i) = j * (j - 1 + t) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, mul_comm, Finset.sum_range_id_mul_two]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  simp_rw [hsum]
  -- show that the set of all numbers j such that there exists an odd t and n = j * (j - 1 + t)
  -- is equal to the set of divisors d of n such that d * d ≤ n and n / d - d is even
  have hs {n} (hn : n ≠ 0) : {j | ∃ t, Odd t ∧ n = j * (j - 1 + t)} = n.divisors.filter (fun d => d * d ≤ n ∧ 2 ∣ n / d - d) := by
    ext j
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Nat.mem_divisors]
    constructor
    · intro ⟨t, ht, hnj⟩
      -- suppose that we have an odd t such that n = j * (j - 1 + t)
      -- we need to show that j is a divisor of n, j * j ≤ n, and n / j - j is even
      -- Odd t implies that t = 2 * k + 1 for some k
      have ⟨k, hk⟩ := ht.exists_bit1
      constructorm* _ ∧ _
      · use j - 1 + t
      · exact hn
      · calc
          j * j ≤ j * (j - 1 + t) := Nat.mul_le_mul (le_refl _) (by omega)
          _ = n := hnj.symm
      · have : 0 < j := by
          contrapose! hn
          rw [hnj, Nat.eq_zero_of_le_zero hn, zero_mul]
        rw [hnj, hk, Nat.mul_div_cancel_left _ this]
        omega
    · intro ⟨⟨hjn, _⟩, hj2, h2⟩
      -- we have j ∣ n, j * j ≤ n, n / j - j is even
      -- and we need to show that there exists an odd number t such that n = j * (j - 1 + t)
      -- use n / j - j + 1 and show that it satisfies the required properties
      use n / j - j + 1
      constructor
      · have ⟨k, hk⟩ := h2
        rw [Odd.eq_1]
        use k
        rw [hk]
      · have hj : 0 < j := by
          contrapose! hjn
          rw [Nat.eq_zero_of_le_zero hjn, Nat.zero_dvd]
          exact hn
        have hj3 : j ≤ j * j := calc
          j = 1 * j := by simp only [one_mul]
          _ ≤ j * j := by apply Nat.mul_le_mul (by omega) (le_refl _)
        simp_rw [mul_add, Nat.mul_sub, Nat.mul_div_cancel_left' hjn, mul_one]
        zify [hj2, hj3]
        ring
  set s := {N : ℕ | _}
  -- it is enough to show that the set from the theorem statement equals to a finite set
  -- defined with a decidable predicate
  suffices s = (Finset.range 1000).filter (fun n => (n.divisors.filter (fun d => d * d ≤ n ∧ 2 ∣ n / d - d)).card = 5) by
    rw [this, Set.ncard_coe_Finset]
    native_decide
  ext n
  simp [s]
  intro hn
  clear s hsum hn
  constructor
  · intro h
    -- it is enough to show that n ≠ 0
    suffices hn : n ≠ 0 by
      rw [hs hn, Set.ncard_coe_Finset] at h
      exact h
    contrapose! h
    -- suppose that n = 0 and show that {j | ∃ t, Odd t ∧ n = j * (j - 1 + t)} = {0}
    suffices {j | ∃ t, Odd t ∧ n = j * (j - 1 + t)} = {0} by
      simp [this, Set.ncard_singleton]
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro ⟨t, ht, hnj⟩
      rw [h, eq_comm, mul_eq_zero] at hnj
      have ⟨k, hk⟩ := ht.exists_bit1
      omega
    · intro hj
      use 1
      simp only [h, odd_one, hj, zero_le, Nat.sub_eq_zero_of_le, zero_add, mul_one, true_and]
  · intro h
    -- is is enough to show that n ≠ 0
    suffices hn : n ≠ 0 by rw [hs hn, Set.ncard_coe_Finset, h]
    contrapose! h
    -- if n = 0 then there are no divisors of n
    simp [h]