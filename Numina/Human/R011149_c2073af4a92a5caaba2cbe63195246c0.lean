import Mathlib

/-If $\frac{m}{2019}$ is a proper fraction, $n$ and $p$ are coprime integers, and $\frac{n}{p}=\frac{m}{2019}$, find the sum of all possible values of $p$.-/
theorem number_theory_632821 (s : Set ℕ) (hs : s = {p : ℕ | ∃(m : ℕ), 0 < m ∧ m < 2019 ∧ ∃(n : ℕ), Nat.Coprime p n ∧ (n : ℚ) / p = m / 2019}) :
  ∑ᶠ p ∈ s, p = 2695 := by
  rw [hs]
  -- Prove that the set s equals {3, 673, 2019}
  have h1 : {p : ℕ | ∃(m : ℕ), 0 < m ∧ m < 2019 ∧ ∃(n : ℕ), Nat.Coprime p n ∧ (n : ℚ) / p = m / 2019} = {3, 673, 2019} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First, we prove the forward direction: if p is in our set, then p is in {3, 673, 2019}
      intro hp
      -- Extract the existential witnesses
      rcases hp with ⟨m, hm1, hm2, n, h2, heq⟩
      -- Prove that p ≠ 0 to avoid division by zero
      have h9: p≠0:=by
        by_contra w
        simp[w] at heq
        have h4:0*2019=((m:ℚ)/2019)*2019:=by congr
        simp at h4
        have h5:m=0:= Rat.natCast_eq_zero.mp (Eq.symm h4)
        omega
      -- Convert the fraction equality to a multiplication equality
      have h3 : (n : ℚ) * 2019 = (m : ℚ) * p := by
        refine (div_eq_div_iff ?_ ?_).mp heq
        by_contra w
        rw[w] at heq
        simp at heq
        exact h9 (Rat.natCast_eq_zero.mp w)
        norm_num
      -- Cast to natural numbers
      have h4 : n * 2019 = m * p := by
        norm_cast at h3 ⊢
      -- Show that p divides n * 2019
      have h5 : p ∣ n * 2019 := by
        use m
        linarith
      -- Since p and n are coprime, p must divide 2019
      have h6 : p ∣ 2019 := (Nat.Coprime.dvd_mul_left h2).mp h5
      -- Prove that p ≠ 1
      have h7:p≠1:=by
        by_contra w
        rw[w] at h4
        omega
      -- Establish bounds on p
      have h8:p>1:=by omega
      have h10:p≤2019:=by
        obtain⟨t,ht⟩:=h6
        rw[ht]
        refine Nat.le_mul_of_pos_right p ?_
        by_contra w
        simp at w
        simp[w] at ht
      -- Use interval_cases to check all divisors of 2019
      interval_cases p <;> norm_num at h6 ⊢
    · -- Now the reverse direction: if p is in {3, 673, 2019}, then p is in our set
      rintro (rfl | rfl | rfl)
      · -- Case p = 3: use m = 673, n = 1
        use 673
        norm_num
        use 1
        norm_num
      · -- Case p = 673: use m = 3, n = 1
        use 3
        norm_num
        use 1
        norm_num
      · -- Case p = 2019: use m = 1, n = 1
        use 1
        norm_num
        use 1
        norm_num
  -- Use the equality to rewrite the sum
  rw [h1]
  -- Convert finsum to finite sum and evaluate
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
