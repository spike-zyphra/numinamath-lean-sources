import Mathlib

/- XXXVII OM - I - Problem 9
Prove that every natural number less than \$ n! \$ is the sum of at most \$ n \$ different natural numbers dividing \$ n! \$. -/

theorem number_theory_124540 (n : ℕ) (k : ℕ) (hk : k < Nat.factorial n) :
    ∃ s : Finset ℕ, s ⊆ Nat.divisors (Nat.factorial n) ∧ k = ∑ i ∈ s, i ∧ s.card ≤ n := by

  -- We will prove this by induction on n.
  induction' n with n ih generalizing k
  -- If n = 0, we can take the empty set.
  · simp only [Nat.factorial_zero, Nat.lt_one_iff] at hk
    use ∅
    constructor
    · simp
    · simp [hk]
  -- We assume the hypothesis for n and prove it for n + 1.
  · -- We write the euclidean division of k by n + 1.
    have : k = (k / (n + 1)) * (n + 1) + k % (n + 1) := by exact Eq.symm (Nat.div_add_mod' k (n + 1))
    -- We have k < (n + 1)! = (n + 1) * n! and k / (n + 1) < n!.
    have hk' : k / (n + 1) < Nat.factorial n := by
      rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos n)]
      rw [mul_comm, ← Nat.factorial_succ]
      exact hk
    -- The multiplication by (n + 1) is injective on ℕ.
    have inj : Function.Injective (fun x => x * (n + 1)) := by
      intro a b hab
      rw [Nat.mul_left_inj (by simp)] at hab
      exact hab
    obtain ⟨s, hs, hsum, hcard⟩ := ih (k / (n + 1)) hk'
    -- We distinguish two cases: either k % (n + 1) = 0 or k % (n + 1) > 0.
    by_cases h : k % (n + 1) = 0
    -- In the first case, we can take the elements of the set s multiplied by (n + 1).
    · use (Finset.map ⟨(fun x => x * (n + 1)), inj⟩ s)
      constructor
      -- They are divisors of (n + 1)! because they are a divisor of n! multiplied by (n + 1).
      · intro x hx
        simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        obtain ⟨m, hm⟩ := (Nat.mem_divisors.mp (hs hy)).1
        simp only [Nat.mem_divisors, ne_eq]
        constructor
        · use m
          rw [Nat.factorial_succ, hm]
          ring
        · exact Nat.factorial_ne_zero (n + 1)
      · constructor
        -- The sum is equal to k because the elements of s are multiplied by (n + 1).
        · rw [Finset.sum_map, Function.Embedding.coeFn_mk]
          nth_rw 1 [this, ← Finset.sum_mul]
          rw [h, add_zero]
          congr
        -- The cardinality is equal to the cardinality of s, which is less than n (and so, less than n+1).
        · rw [Finset.card_map]
          linarith
    -- In the second case, we can take the elements of the set s multiplied by (n + 1) and add k % (n + 1).
    · use (Finset.map ⟨(fun x => x * (n + 1)), inj⟩ s) ∪ { k % (n + 1) }
      constructor
      · intro x hx
        simp only [Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk,
          Finset.mem_singleton] at hx
        rcases hx with hx | hx
        -- The elements of s multiplied by (n + 1) are divisors of (n + 1)!.
        · obtain ⟨y, hy, rfl⟩ := hx
          obtain ⟨m, hm⟩ := (Nat.mem_divisors.mp (hs hy)).1
          simp only [Nat.mem_divisors, ne_eq]
          constructor
          · use m
            rw [Nat.factorial_succ, hm]
            ring
          · exact Nat.factorial_ne_zero (n + 1)
        -- The element k % (n + 1) is a divisor of (n + 1)! because it is less than n + 1.
        · have : x < n + 1 := by rw [hx]; exact Nat.mod_lt k (Nat.succ_pos n)
          simp only [Nat.mem_divisors, ne_eq]
          constructor
          · apply Nat.dvd_factorial ?_ (Nat.le_of_succ_le this)
            simp only [nonpos_iff_eq_zero] at this
            rw [← hx] at h
            omega
          · exact Nat.factorial_ne_zero (n + 1)
      -- The remainder of the division is less than n+1, so it's not in the set of elements multiplied by (n + 1).
      · have disj : Disjoint (Finset.map { toFun := fun x ↦ x * (n + 1), inj' := inj } s) {k % (n + 1)} := by
          simp only [Finset.disjoint_singleton_right, Finset.mem_map,
            Function.Embedding.coeFn_mk, not_exists, not_and]
          intro x hx
          apply ne_of_gt
          apply lt_of_lt_of_le (Nat.mod_lt k (Nat.succ_pos n)) (by
            simp only [Nat.succ_eq_add_one, add_pos_iff, zero_lt_one, or_true,
              le_mul_iff_one_le_left, Nat.one_le_iff_ne_zero]
            obtain ⟨m, hm⟩ := (Nat.mem_divisors.mp (hs hx)).1
            by_contra!
            rw [this, zero_mul] at hm
            exact Nat.factorial_ne_zero n hm
              )
        constructor
        -- The sum is equal to k because the elements of s are multiplied by (n + 1) and we add k % (n + 1).
        · rw [Finset.sum_union]
          · simp only [Finset.sum_map, Function.Embedding.coeFn_mk, Finset.sum_singleton]
            nth_rw 1 [this, ← Finset.sum_mul]
            congr
          · exact disj
        -- The cardinality is equal to the cardinality of s plus one, so it is less than n+1.
        · rw [Finset.card_union_of_disjoint disj]
          simp [Finset.card_map, hcard]